#pragma once
#include "Term.h"

struct PropagatorBase;

struct equalityPair {
    const Term* lhs;
    const Term* rhs;
    unsigned lhsCpy;
    unsigned rhsCpy;

    equalityPair(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) : lhs(lhs), rhs(rhs), lhsCpy(lhsCpy), rhsCpy(rhsCpy) { }

    inline bool operator==(const equalityPair& other) const {
        return lhs == other.lhs && rhs == other.rhs && lhsCpy == other.lhsCpy && rhsCpy == other.rhsCpy;
    }

    inline bool operator!=(const equalityPair& other) const {
        return !this->operator==(other);
    }

    inline string to_string() const {
        return "<" + lhs->to_string() + "#" + std::to_string(lhsCpy) + " = " + rhs->to_string() + "#" + std::to_string(rhsCpy) + ">";
    }
};

struct LazySubDiseq : public equalityPair{
    bool processed;

    LazySubDiseq() : equalityPair(nullptr, 0, nullptr, 0), processed(false) { }

    LazySubDiseq(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) : equalityPair(lhs, lhsCpy, rhs, rhsCpy), processed(false) { }

    inline string ToString() const {
        return lhs->to_string() + "#" + std::to_string(lhsCpy) + " != " + rhs->to_string() + "#" + std::to_string(rhsCpy);
    }
};


namespace std {
    template <>
    struct hash<equalityPair> {
        size_t operator()(const equalityPair& x) const;
    };
}

class ComplexADTSolver {

    vector<string> SortNames;

    unordered_map<string, SimpleADTSolver*> nameToSolver;
    unordered_map<literal, equalityPair> exprToEq;
    unordered_map<equalityPair, literal> eqToExpr;
    unordered_map<literal, Term*> exprToTerm;
    unordered_map<literal, bool> interpretation;

public:

    vector<SimpleADTSolver*> Solvers;

    const bool SATSplit;
    PropagatorBase* propagator = nullptr;

    inline unsigned getSortCnt() const {
        return SortNames.size();
    }

    ComplexADTSolver() = delete;
    ComplexADTSolver(ComplexADTSolver&) = delete;
    ComplexADTSolver& operator=(ComplexADTSolver&) = delete;

    ComplexADTSolver(bool z3Split);

    ~ComplexADTSolver();

    SimpleADTSolver* NewSolver(const string& name);

    string GetSolverName(unsigned solverId) {
        return SortNames[solverId];
    }

    SimpleADTSolver* GetSolver(const string& name);

    bool Asserted(literal e, bool isTrue);

    bool Asserted(literal e, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy, bool isTrue);

    literal MakeEqualityExpr(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy);

    literal MakeDisEqualityExpr(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy);

    void PeekTerm(const string& solver, const string& name, int argCnt);

    static bool AreEqual(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy);

    string GetModel() const;

    void MakeZ3ADT(z3::context& ctx);

    inline bool GetEq(literal l, equalityPair& value) {
        return tryGetValue(exprToEq, l, value);
    }

    z3::sort& GetZ3Sort(const string& name);
};

struct LazyDiseq {
    vector<LazySubDiseq> SubDisequalities;
    unsigned IrrelevantDisequalitiesCnt;
    vector<literal> Justifications;
    bool Solved;

    LazyDiseq() : SubDisequalities(), IrrelevantDisequalitiesCnt(0), Justifications(), Solved(false) { }
};

struct SimpleADTSolver {

    ComplexADTSolver& ComplexSolver;

    inline PropagatorBase& propagator() const {
        return *ComplexSolver.propagator;
    }

    optional<z3::sort> Z3Sort;
    const unsigned SolverId;
    vector<std::vector<unsigned>> Domains;
    vector<string> FuncNames;
    vector<string> VarNames;

    unordered_map<string, int> nameToId;
    unordered_map<RawTermWrapper, Term*> hashCon;

    // substitution[v][i] means that copy i of variable v is mapped to copy cpy of term subst with justification just
    vector<pvector<substitution>> substitutionList;
    // List of all disequalities that could not be eliminated instantly.
    // Each disequality consists of sub-disequalities
    pvector<LazyDiseq> diseqList;
    vector<vector<unordered_set<unsigned>>> observerList; // observe lazy disequalities per variable and cpy

    SimpleADTSolver(ComplexADTSolver& complexSolver, unsigned id) : ComplexSolver(complexSolver), SolverId(id) { }

    ~SimpleADTSolver();

    string PrettyPrint(const Term* t, unsigned cpyIdx, unordered_map<variableIdentifier, string>* prettyNames) const;

    void EnsureFounded();

    bool GetSubstitution(int id, unsigned cpy, substitution*& t);

    bool SetSubstitution(int id, unsigned cpy, const Term* subst, unsigned substCpy, vector<literal>& just, bool probe);

    int PeekTerm(const string& name, unsigned argCnt);
    int PeekTerm(const string& name, vector<unsigned> domain);

    inline Term* MakeTerm(const string& name, const pvector<Term>& args) {
        return MakeTerm(PeekTerm(name, args.size()), args);
    }

    Term* MakeTerm(int id, const pvector<Term>& args);
    Term* MakeTermInternal(int id, const pvector<Term>& args);
    Term* MakeVar(const string& name);
    Term* MakeVar(int idx);

    inline int GetId(const string& name) const {
        return nameToId.at(name);
    }

    bool Unify(literal just, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
        vector<literal> justList;
        justList.push_back(just);
        return Unify(lhs, lhsCpy, rhs, rhsCpy, justList);
    }
    bool Unify(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy, vector<literal>& justifications);
    bool CheckCycle(const RawTerm* t, unsigned cpy, int assignmentId, unsigned assignmentCpyId, vector<literal>& justifications);
    bool AreEqual(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy);
    bool NonUnify(literal just, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy);
    bool NonUnify(bool skipRoot, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy,
                  vector<literal>& justifications, vector<LazySubDiseq>& delayed, vector<observerItem>& observerUpdates);

    string ToString() const;

    optional<term_instance> GetModel(int varId, unsigned copyIdx) const;
    string GetModel();
};
