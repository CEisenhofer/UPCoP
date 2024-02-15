#pragma once
#include "PropagatorBase.h"
#include <utility>

struct path_element {
    const IndexedClause& clause;
    int cpy;
    const GroundLiteral lit;

    path_element(const IndexedClause& clause, int cpy, const GroundLiteral& lit) : clause(clause), cpy(cpy), lit(lit) {}
};

struct clause_instance {
    const IndexedClause* clause;
    const unsigned copy_idx;
    const literal selector;
    tri_state value;
    const vector<GroundLiteral> literals;

    clause_instance() = delete;
    clause_instance(clause_instance& other) = delete;
    auto operator=(clause_instance& other) = delete;

    clause_instance(const IndexedClause* clause, unsigned copyIdx, literal selectionExpr, vector<GroundLiteral> literals) :
            clause(clause), copy_idx(copyIdx), selector(selectionExpr), value(undef), literals(std::move(literals)) { }

    /*vector<literal> GetVariables(PropagatorBase& propagator, DatatypeSort[] sorts) {
        vector<literal> variables;
        variables.resize(sorts.size());
        for (int i = 0; i < variables.size(); i++) {
            variables[i] = propagator.new_observed_var("arg" + i, sorts[i]);
        }
        return variables;
    }*/

    string to_string() const { return std::to_string(copy_idx + 1) + ". copy of clause #" + std::to_string(clause->Index); }
};

class matrix_propagator : public PropagatorBase {

    vector<vector<clause_instance*>> cachedClauses;
    vector<unsigned> multiplicity;
    vector<unsigned> priority;

    unordered_set<z3::func_decl> variableSet;

    vector<clause_instance*> allClauses;
    vector<clause_instance*> chosen;
    vector<clause_instance*> not_chosen;

    unordered_map<literal, clause_instance*> exprToInfo;
    unordered_map<literal, int> clauseLimitMap;
    vector<literal> clauseLimitListExpr;
    unsigned lvl;

    int finalCnt = 0;

public:
    matrix_propagator(CNF<IndexedClause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt);

    ~matrix_propagator() override {
        for (auto& clause : allClauses) {
            delete clause;
        }
    }

    void next_level() {
        lvl++;
        reinit_solver();
        if (progParams.Mode == Rectangle)
            next_level_rect();
        else
            next_level_core();
    }

private:
    void next_level_rect(unsigned inc_lvl = 1);
    void next_level_core();

public:

    clause_instance* GetClauseInstanceInfo(const IndexedClause* clause, unsigned cpyIdx, literal selector);

    bool AreConnected(const GroundLiteral& l1, const GroundLiteral& l2);

    void CheckProof(z3::solver& uniSolver, const vector<clause_instance*>& chosen);

    clause_instance* GetGround(const IndexedClause* clause, unsigned cpy);

    void AssertRoot();

    void pb_clause_limit();

    void fixed2(literal e, bool value) override;

    void PropagateRules(literal e, clause_instance* info) {
        for (auto& lit : info->literals) {
            propagate({ e }, ConnectLiteral(info, lit));
        }
    }

    formula ConnectLiteral(clause_instance* info, const GroundLiteral& lit);

    void final() override;

    void FindPath(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path, vector<vector<path_element>>& foundPaths, int limit);

    void PrintProof(z3::solver& uniSolver, unordered_map<variableIdentifier, string>& prettyNames, unordered_map<unsigned, int>& usedClauses) {
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
                        if (!AreConnected(chosen[i]->literals[k], chosen[j]->literals[l]))
                            continue;

                        std::cout << "Connected: &" << clauseToCnt[chosen[i]] << ": " << PrettyPrintLiteral(chosen[i]->literals[k], &prettyNames) << " and &" << clauseToCnt[chosen[j]] << ": " << PrettyPrintLiteral(chosen[j]->literals[l], &prettyNames) << "\n";

                        for (int m = 0; m < chosen[i]->literals[k].GetArity(); m++) {
                            bool res = term_solver.Asserted(this->m.mk_true(),
                                                            chosen[i]->literals[k].Literal->ArgBases[m], chosen[i]->copy_idx,
                                                            chosen[j]->literals[l].Literal->ArgBases[m], chosen[j]->copy_idx, true);
                            if (!res)
                                throw solving_exception("Failed unification");
                        }
                    }
                }
            }
        }

        CheckProof(uniSolver, chosen);
    }
};
