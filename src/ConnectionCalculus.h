#include "CLIParser.h"
#include "cnf.h"
#include "adt_solver.h"

class Abstraction {
protected:
    simple_adt_solver* solver;

    Abstraction() = default;

    Abstraction(simple_adt_solver* solver) : solver(solver) {}

public:
    virtual const term* apply(const vector<const term*>& args) const = 0;
};

class variable_abstraction : public Abstraction {

    term* var;

public:

    variable_abstraction() = default;

    variable_abstraction(simple_adt_solver* solver, term* var) : Abstraction(solver), var(var) {
        assert(var->FuncID < 0);
    }

    const term* apply(const vector<const term*>& args) const override;
};

class term_abstraction : public Abstraction {

    int termId;

public:

    term_abstraction() = default;

    term_abstraction(simple_adt_solver* solver, int termId) : Abstraction(solver), termId(termId) {}

    const term* apply(const vector<const term*>& args) const override;
};

tri_state solve(const string& path, ProgParams& progParams, bool silent);

static cnf<indexed_clause*> to_cnf(const z3::expr& input, complex_adt_solver& adtSolver, unsigned& literalCnt);

cnf<clause> to_cnf(z3::context& ctx, const z3::expr& input, bool polarity, z3::expr_vector& scopeVars, z3::sort_vector& scopeSorts,
                   z3::expr_vector& substitutions, unordered_set<optional<z3::func_decl>>& terms, unordered_map<string, unsigned>& nameCache, unordered_set<unsigned>& visited);

void CollectTerm(const z3::expr& expr, unordered_set<optional<z3::func_decl>>& language,
                 std::unordered_set<unsigned>& visited);

const term* substitute_term(const z3::expr& expr,
                      const unordered_map<z3::func_decl, term_abstraction>& termAbstraction,
                      const unordered_map<z3::func_decl, variable_abstraction>& varAbstraction);
