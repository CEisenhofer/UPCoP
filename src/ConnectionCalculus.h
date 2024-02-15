#include "CLIParser.h"
#include "CNF.h"
#include "ADTSolver.h"
#include "CadicalWrapper.h"

class Abstraction {
protected:
    SimpleADTSolver* solver;

    Abstraction() = default;

    Abstraction(SimpleADTSolver* solver) : solver(solver) {}

public:
    virtual Term* Apply(const pvector<Term>& args) const = 0;
};

class VariableAbstraction : public Abstraction {

    int id;

public:

    VariableAbstraction() = default;

    VariableAbstraction(SimpleADTSolver* solver, Term* variable) : Abstraction(solver), id(variable->FuncID) {
        assert(variable->FuncID < 0);
    }

    Term* Apply(const pvector<Term>& args) const override;
};

class TermAbstraction : public Abstraction {

    int termId;

public:

    TermAbstraction() = default;

    TermAbstraction(SimpleADTSolver* solver, int termId) : Abstraction(solver), termId(termId) {}

    Term* Apply(const pvector<Term>& args) const override;
};

tri_state solve(const string& path, ProgParams& progParams, bool silent);

static CNF<IndexedClause*> ToCNF(const z3::expr& input, ComplexADTSolver& adtSolver, unsigned& literalCnt);

CNF<Clause> ToCNF(z3::context& ctx, const z3::expr& input, bool polarity, z3::expr_vector& scopeVars, z3::sort_vector& scopeSorts,
      z3::expr_vector& substitutions, unordered_set<optional<z3::func_decl>>& terms, unordered_map<string, unsigned>& nameCache, unordered_set<unsigned>& visited);

void CollectTerm(const z3::expr& expr, unordered_set<optional<z3::func_decl>>& language,
                 std::unordered_set<unsigned>& visited);

Term* SubstituteTerm(const z3::expr& expr,
                     const unordered_map<z3::func_decl, TermAbstraction>& termAbstraction,
                     const unordered_map<z3::func_decl, VariableAbstraction>& varAbstraction);
