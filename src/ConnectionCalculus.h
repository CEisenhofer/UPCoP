#include "CLIParser.h"
#include "cnf.h"
#include "ADTSolver.h"
#include "CadicalWrapper.h"

class Abstraction {
protected:
    SimpleADTSolver* solver;

    Abstraction() = default;

    Abstraction(SimpleADTSolver* solver) : solver(solver) {}

public:
    virtual term* Apply(const pvector<term>& args) const = 0;
};

class variable_abstraction : public Abstraction {

    int id;

public:

    variable_abstraction() = default;

    variable_abstraction(SimpleADTSolver* solver, term* variable) : Abstraction(solver), id(variable->FuncID) {
        assert(variable->FuncID < 0);
    }

    term* Apply(const pvector<term>& args) const override;
};

class term_abstraction : public Abstraction {

    int termId;

public:

    term_abstraction() = default;

    term_abstraction(SimpleADTSolver* solver, int termId) : Abstraction(solver), termId(termId) {}

    term* Apply(const pvector<term>& args) const override;
};

tri_state solve(const string& path, ProgParams& progParams, bool silent);

static cnf<indexed_clause*> to_cnf(const z3::expr& input, ComplexADTSolver& adtSolver, unsigned& literalCnt);

cnf<clause> to_cnf(z3::context& ctx, const z3::expr& input, bool polarity, z3::expr_vector& scopeVars, z3::sort_vector& scopeSorts,
                   z3::expr_vector& substitutions, unordered_set<optional<z3::func_decl>>& terms, unordered_map<string, unsigned>& nameCache, unordered_set<unsigned>& visited);

void CollectTerm(const z3::expr& expr, unordered_set<optional<z3::func_decl>>& language,
                 std::unordered_set<unsigned>& visited);

term* SubstituteTerm(const z3::expr& expr,
                     const unordered_map<z3::func_decl, term_abstraction>& termAbstraction,
                     const unordered_map<z3::func_decl, variable_abstraction>& varAbstraction);
