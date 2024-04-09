#pragma once
#include "propagator_base.h"

struct clause_instance {
    const indexed_clause* clause;
    const unsigned copyIdx;
    const literal selector;
#ifndef PUSH_POP
    bool propagated;
#endif
    tri_state value;
    const vector<ground_literal> literals;
    vector<equality> delayedRelevantTrue;
    vector<equality> delayedRelevantFalse;
    vector<less_than> delayedRelevantLess;

    // for reachability
    clause_instance* parent;
    clause_instance* prev_sibling;
    clause_instance* next_sibling;

    clause_instance() = delete;
    clause_instance(clause_instance& other) = delete;
    auto operator=(clause_instance& other) = delete;

    clause_instance(const indexed_clause* clause, unsigned copyIdx, literal selectionExpr, vector<ground_literal> literals) :
            clause(clause), copyIdx(copyIdx), selector(selectionExpr),
#ifndef PUSH_POP
            propagated(false),
#endif
            value(undef), literals(std::move(literals)),
            parent(this), prev_sibling(this), next_sibling(this) { }

    inline bool is_root() const {
        return parent == this;
    }

    inline clause_instance* find_root(propagator_base& propagator) {
        clause_instance* current = this;
        while (current != current->parent) {
            current = current->parent;
        }
        if (current == parent)
            return current;

        auto* prev = parent;
        propagator.add_undo([this, prev]() { parent = prev; });
        parent = current;
        return current;
    }

    static void merge_root(clause_instance* b, clause_instance* newRoot, propagator_base& propagator) {
        assert(b->is_root());
        assert(newRoot->is_root());
        assert(b != newRoot);

        auto* p = newRoot->prev_sibling;
        auto* n = b->next_sibling;

        b->next_sibling = newRoot;
        newRoot->prev_sibling = b;

        p->next_sibling = n;
        n->prev_sibling = p;

        propagator.add_undo([b, newRoot, p, n]() {
            b->parent = b;

            newRoot->prev_sibling = p;
            p->next_sibling = newRoot;

            b->next_sibling = n;
            n->prev_sibling = b;
        });
        b->parent = newRoot;
    }

    string to_string() const { return std::to_string(copyIdx + 1) + ". copy of clause #" + std::to_string(clause->Index); }
};

struct path_element {
    const clause_instance& clause;
    const ground_literal lit;

    path_element(const clause_instance& clause, const ground_literal& lit) : clause(clause), lit(lit) {}
};

class matrix_propagator : public propagator_base {

    vector<vector<clause_instance*>> cachedClauses;

    unordered_set<z3::func_decl> variableSet;

    vector<clause_instance*> allClauses;
    vector<clause_instance*> chosen;
    vector<clause_instance*> not_chosen;

    unordered_map<literal, clause_instance*> exprToInfo;
    unordered_map<literal, int> clauseLimitMap;
    vector<literal> clauseLimitListExpr;
    const unsigned lvl;

    int finalCnt = 0;

    bool hasLimFalse = false;
    bool pbPropagated = false;

public:
    matrix_propagator(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft);

    ~matrix_propagator() override;

    bool next_level() {
        progParams.depth = lvl + 1;

        if (progParams.mode == Core)
            return next_level_core();

        assert(progParams.mode == Rectangle);
        for (unsigned i = 0; i < matrix.size(); i++) {
            if (matrix[i]->Ground && progParams.multiplicity[i] > 0)
                continue;
            progParams.multiplicity[i] = progParams.depth;
        }
        return false;
    }

    inline unsigned get_final_cnt() const {
        return finalCnt;
    }

private:

    void create_instances();

    bool next_level_core();

public:

    clause_instance* create_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector);

    bool are_same_atom(const ground_literal& l1, const ground_literal& l2);

    bool are_connected(const ground_literal& l1, const ground_literal& l2) {
        return l1.lit->polarity != l2.lit->polarity && are_same_atom(l1, l2);
    }

    void check_proof(z3::context& ctx);

    clause_instance* get_ground(const indexed_clause* clause, unsigned cpy);

    void assert_root();

    void pb_clause_limit();

    void fixed(literal e, bool value);

    bool delayed_rp(clause_instance* info);

    bool propagate_rules(literal e, clause_instance* info) {
        start_watch(connect_time);
        justification just(e);
        for (const auto& lit : info->literals) {
            if (!hard_propagate(just, connect_literal(e, info, lit))) {
                stop_watch(connect_time);
                return false;
            }
        }
        stop_watch(connect_time);
        return true;
    }

    formula connect_literal(literal just, clause_instance* info, const ground_literal& lit);

    void final() override;

    void find_path(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path, vector<vector<path_element>>& foundPaths, unsigned& steps);

    void find_path_sat(const vector<clause_instance*>& clauses, vector<vector<path_element>>& foundPaths);

    void print_proof(unordered_map<term_instance*, string>& prettyNames, unordered_map<unsigned, int>& usedClauses) {
        int clauseCnt = 1;
        unordered_map<clause_instance*, int> clauseToCnt;
        sort(chosen.begin(), chosen.end(), [](const clause_instance* c1, const clause_instance* c2) {
            if (c1->clause->Index == c2->clause->Index)
                return c1->copyIdx < c2->copyIdx;
            return c1->clause->Index < c2->clause->Index;
        });

        for (auto& clause : chosen) {
            clauseToCnt.insert(make_pair(clause, clauseCnt));
            std::cout << "Clause &" << clauseCnt++ << " (#" << clause->clause->Index << "/" << clause->copyIdx << "): " << clause_to_string(clause->literals, &prettyNames) << "\n";
            int cnt = 0;
            if (tryGetValue(usedClauses, clause->clause->Index, cnt))
                usedClauses[clause->clause->Index] = cnt + 1;
            else
                usedClauses.insert(make_pair(clause->clause->Index, 1));
        }

        // TODO: Do we really need that many loops?
        for (int i = 0; i < chosen.size(); i++) {
            for (int j = i; j < chosen.size(); j++) {

                for (int k = 0; k < chosen[i]->literals.size(); k++) {
                    for (int l = 0; l < chosen[j]->literals.size(); l++) {
                        if (!are_connected(chosen[i]->literals[k], chosen[j]->literals[l]))
                            continue;

                        std::cout << "Connected: &" << clauseToCnt[chosen[i]] << ": " << pretty_print_literal(chosen[i]->literals[k], &prettyNames) << " and &" << clauseToCnt[chosen[j]] << ": " << pretty_print_literal(
                                chosen[j]->literals[l], &prettyNames) << "\n";

                        for (int m = 0; m < chosen[i]->literals[k].arity(); m++) {
                            justification just;
                            auto* lhs = chosen[i]->literals[k].lit->arg_bases[m]->get_instance(chosen[i]->copyIdx, *this);
                            auto* rhs = chosen[i]->literals[k].lit->arg_bases[m]->get_instance(chosen[i]->copyIdx, *this);
                            bool res = lhs->t->solver.unify(lhs, rhs, just);
                            if (!res)
                                throw solving_exception("Failed unification");
                        }
                    }
                }
            }
        }
        std::flush(std::cout);
    }

};
