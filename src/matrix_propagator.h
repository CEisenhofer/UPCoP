#pragma once
#include "propagator_base.h"

struct path_element {
    const indexed_clause& clause;
    int cpy;
    const ground_literal lit;

    path_element(const indexed_clause& clause, int cpy, const ground_literal& lit) : clause(clause), cpy(cpy), lit(lit) {}
};

struct clause_instance {
    const indexed_clause* clause;
    const unsigned copy_idx;
    const literal selector;
    bool propagated;
    tri_state value;
    const vector<ground_literal> literals;

    clause_instance() = delete;
    clause_instance(clause_instance& other) = delete;
    auto operator=(clause_instance& other) = delete;

    clause_instance(const indexed_clause* clause, unsigned copyIdx, literal selectionExpr, vector<ground_literal> literals) :
            clause(clause), copy_idx(copyIdx), selector(selectionExpr), propagated(false), value(undef), literals(std::move(literals)) { }

    /*vector<literal> GetVariables(PropagatorBase& propagator, DatatypeSort[] sorts) {
        vector<literal> variables;
        variables.resize(sorts.size());
        for (int i = 0; i < variables.size(); i++) {
            variables[i] = propagator.new_observed_var(OPT("arg" + i, sorts[i]));
        }
        return variables;
    }*/

    string to_string() const { return std::to_string(copy_idx + 1) + ". copy of clause #" + std::to_string(clause->Index); }
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

public:
    matrix_propagator(cnf<indexed_clause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt);

    ~matrix_propagator() override {
        for (auto& clause : allClauses) {
            delete clause;
        }
    }

    bool next_level() {
        progParams.Depth = lvl + 1;

        if (progParams.Mode == Core)
            return next_level_core();

        assert(progParams.Mode == Rectangle);
        for (unsigned i = 0; i < matrix.size(); i++) {
            if (matrix[i]->Ground && progParams.multiplicity[i] > 0)
                continue;
            progParams.multiplicity[i] = progParams.Depth;
        }
        return false;
    }

private:

    void create_instances();

    bool next_level_core();

public:

    clause_instance* get_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector);

    bool are_connected(const ground_literal& l1, const ground_literal& l2);

    void check_proof(const vector<clause_instance*>& chosen);

    clause_instance* GetGround(const indexed_clause* clause, unsigned cpy);

    void assert_root();

    void pb_clause_limit();

    void fixed2(literal e, bool value) override;

    bool PropagateRules(literal e, clause_instance* info) {
        for (const auto& lit : info->literals) {
            if (!hard_propagate({ e }, connect_literal(info, lit)))
                return false;
        }
        return true;
    }

    formula connect_literal(clause_instance* info, const ground_literal& lit);

    void final() override;

    void FindPath(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path, vector<vector<path_element>>& foundPaths, int limit);

    void PrintProof(z3::solver& uniSolver, unordered_map<term_instance*, string>& prettyNames, unordered_map<unsigned, int>& usedClauses) {
        int clauseCnt = 1;
        unordered_map<clause_instance*, int> clauseToCnt;
        sort(chosen.begin(), chosen.end(), [](const clause_instance* c1, const clause_instance* c2) {
            if (c1->clause->Index == c2->clause->Index)
                return c1->copy_idx < c2->copy_idx;
            return c1->clause->Index < c2->clause->Index;
        });

        for (auto& clause : chosen) {
            clauseToCnt.insert(make_pair(clause, clauseCnt));
            std::cout << "Clause &" << clauseCnt++ << " (#" << clause->clause->Index << "/" << clause->copy_idx << "): " << ClauseToString(clause->literals, &prettyNames) << "\n";
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

                        std::cout << "Connected: &" << clauseToCnt[chosen[i]] << ": " << PrettyPrintLiteral(chosen[i]->literals[k], &prettyNames) << " and &" << clauseToCnt[chosen[j]] << ": " << PrettyPrintLiteral(chosen[j]->literals[l], &prettyNames) << "\n";

                        for (int m = 0; m < chosen[i]->literals[k].GetArity(); m++) {
                            bool res = term_solver.Asserted(this->m.mk_true(),
                                                            chosen[i]->literals[k].Literal->arg_bases[m]->GetInstance(chosen[i]->copy_idx),
                                                            chosen[j]->literals[l].Literal->arg_bases[m]->GetInstance(chosen[j]->copy_idx), true);
                            if (!res)
                                throw solving_exception("Failed unification");
                        }
                    }
                }
            }
        }

        check_proof(chosen);
    }

};
