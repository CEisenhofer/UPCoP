#pragma once
#include "term.h"

struct propagator_base;

class ComplexADTSolver {

    vector<string> SortNames;

    unordered_map<string, SimpleADTSolver*> nameToSolver;
    unordered_map<literal, equality> exprToEq;
    unordered_map<literal, lessThan> exprToLess;
    unordered_map<equality, literal> eqToExpr;
    unordered_map<lessThan, literal> lessToExpr;

    unordered_map<literal, bool> interpretation;

public:

    vector<SimpleADTSolver*> Solvers;

    propagator_base* propagator = nullptr;

    inline unsigned getSortCnt() const {
        return SortNames.size();
    }

    ComplexADTSolver() = default;

    ComplexADTSolver(ComplexADTSolver&) = delete;
    ComplexADTSolver& operator=(ComplexADTSolver&) = delete;

    ~ComplexADTSolver();

    SimpleADTSolver* NewSolver(const string& name);

    string GetSolverName(unsigned solverId) {
        return SortNames[solverId];
    }

    SimpleADTSolver* GetSolver(const string& name);

    bool Asserted(literal e, bool isTrue);

    bool Asserted(literal e, term_instance* lhs, term_instance* rhs, bool isTrue) const;

    literal MakeEqualityExpr(term_instance* lhs, term_instance* rhs);
    literal MakeDisEqualityExpr(term_instance* lhs, term_instance* Rhs);

    literal MakeLessExpr(term_instance* lhs, term_instance* rhs);
    literal MakeGreaterEqExpr(term_instance* lhs, term_instance* rhs);

    literal MakeLessEqExpr(term_instance* lhs, term_instance* rhs) {
        return MakeGreaterEqExpr(rhs, lhs);
    }
    literal MakeGreaterExpr(term_instance* lhs, term_instance* rhs) {
        return MakeLessExpr(rhs, lhs);
    }

    void PeekTerm(const string& solver, const string& name, int argCnt);

    static bool AreEqual(term_instance* lhs, term_instance* rhs);
};

struct SimpleADTSolver {

    ComplexADTSolver& ComplexSolver;

    inline propagator_base& propagator() const {
        return *ComplexSolver.propagator;
    }

    optional<z3::sort> Z3Sort;
    const unsigned SolverId;
    vector<std::vector<unsigned>> Domains;
    vector<string> FuncNames;
    vector<string> VarNames;

    unordered_map<string, int> nameToId;
    unordered_map<RawTermWrapper, term*> hashCon;

    SimpleADTSolver(ComplexADTSolver& complexSolver, unsigned id) : ComplexSolver(complexSolver), SolverId(id) { }

    ~SimpleADTSolver();

private:

    void Conflict(const vector<Justification*>& just);
    void Propagate(const vector<Justification*>& just, formula prop);

public:

    string PrettyPrint(const term* t, unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const;

    int PeekTerm(const string& name, unsigned argCnt);
    int PeekTerm(const string& name, vector<unsigned> domain);

    inline term* MakeTerm(const string& name, const pvector<term>& args) {
        return MakeTerm(PeekTerm(name, args.size()), args);
    }

    term* MakeTerm(int id, const pvector<term>& args);
    term* MakeTermInternal(int id, const pvector<term>& args);
    term* MakeVar(const string& name);
    term* MakeVar(int idx);

    inline int GetId(const string& name) const {
        return nameToId.at(name);
    }

private:

    bool UpdateDiseq(term_instance* b, term_instance* newRoot);
    bool UpdateIneq(term_instance* newRoot);

public:
    bool Unify(literal just, term_instance* lhs, term_instance* rhs);
    bool NonUnify(literal just, term_instance* lhs, term_instance* rhs);
    bool Less(literal just, term_instance* lhs, term_instance* rhs, bool eq);

    bool AreEqual(term_instance* lhs, term_instance* rhs);

private:

    bool Unify(term_instance* lhs, term_instance* rhs, vector<Justification*>& justifications);
    z3::check_result NonUnify(Lazy* lazy);


    bool CheckCycle(term_instance* inst, vector<Justification*>& justifications);
    bool CheckCycle(term_instance* inst, term_instance* search, vector<Justification*>& justifications);
    bool Check(term_instance* start, term_instance* current, bool eq, vector<Justification*>& just, vector<term_instance*>& path, bool smaller);


    bool AddRoot(term_instance* b, term_instance* newRoot, bool incIneq = true);
    bool MergeRoot(term_instance* r1, term_instance* r2, equality& eq, bool incIneq = true);

public:
    static void FindJust(term_instance* n1, term_instance* n2, vector<Justification*>& minimalJust);

    string to_string() const;
};
