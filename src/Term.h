#pragma once
#include "CadicalWrapper.h"
#include "utils.h"

struct Term;
struct term_instance;
struct SimpleADTSolver;
struct SubtermHint;

struct observerItem {
    int idx;
    int cpy;

    observerItem(int idx, int cpy) : idx(idx), cpy(cpy) { }
};

struct variableIdentifier {
    unsigned solverId;
    int id;
    unsigned cpyIdx;

    variableIdentifier(unsigned solverId, int id, unsigned cpyIdx) : solverId(solverId), id(id), cpyIdx(cpyIdx) { }

    variableIdentifier(const variableIdentifier&) = default;

    bool operator==(const variableIdentifier& other) const {
        return solverId == other.solverId && id == other.id && cpyIdx == other.cpyIdx;
    }
    bool operator!=(const variableIdentifier& other) const {
        return !this->operator==(other);
    }
};

namespace std {
    template <>
    struct hash<variableIdentifier> {
        size_t operator()(const variableIdentifier& x) const;
    };
}

struct substitution {
    const Term* subst;
    const unsigned cpy;
    const vector<literal> just;

    substitution(const Term* subst, unsigned cpy, vector<literal>& just) : subst(subst), cpy(cpy), just(just) { }
};

struct RawTerm {
    int FuncID;
    const pvector<Term> Args;

    RawTerm(int funcId, pvector<Term> args) : FuncID(funcId), Args(std::move(args)) {
    }

    bool operator==(const RawTerm& other) const {
        if (FuncID != other.FuncID || Args.size() != other.Args.size())
            return false;
        for (unsigned i = 0; i < Args.size(); i++)
            if (Args[i] != other.Args[i])
                return false;
        return true;
    }
    bool operator!=(const RawTerm& other) const {
        return !this->operator==(other);
    }
};

namespace std {
    template <>
    struct hash<RawTerm> {
        size_t operator()(const RawTerm& x) const;
    };
}

struct RawTermWrapper {
    const RawTerm* obj;

    RawTermWrapper(const RawTerm* obj) : obj(obj) { }

    bool operator==(const RawTermWrapper& other) const {
        return *obj == *other.obj;
    }
    bool operator!=(const RawTermWrapper& other) const {
        return !this->operator==(other);
    }
};

namespace std {
    template <>
    struct hash<RawTermWrapper> {
        size_t operator()(const RawTermWrapper& x) const {
            static hash<RawTerm> hash;
            return hash(*x.obj);
        }
    };
}

struct Term : public RawTerm {
    const unsigned HashID;
    const bool Ground;
    optional<z3::expr> Z3Expr;
    SimpleADTSolver& Solver;

    unsigned getSolverId() const;

    bool operator==(const Term& other) const {
        return getSolverId() == other.getSolverId() && HashID == other.HashID;
    }

    bool operator!=(const Term& other) const {
        return !this->operator==(other);
    }

    Term(int funcId, pvector<Term> args, SimpleADTSolver& solver, unsigned hashId);

    Term(const Term&) = delete;

    bool SeemsPossiblyUnifiable(Term* rhs, SubtermHint& hint);

    string to_string() const;

    string PrettyPrint(unsigned cpyIdx, unordered_map<variableIdentifier, string>* prettyNames) const;
};

namespace std {
    template <>
    struct hash<Term> {
        size_t operator()(const Term& x) const;
    };
}

struct term_instance {
    const Term* term;
    const unsigned cpyIdx;

    term_instance(const Term* term, unsigned cpyIdx) : term(term), cpyIdx(cpyIdx) { }

    inline bool operator==(const term_instance& other) const {
        return *term == *other.term && cpyIdx == other.cpyIdx;
    }

    inline bool operator!=(const term_instance& other) const {
        return !this->operator==(other);
    }
};

namespace std {
    template <>
    struct hash<term_instance> {
        size_t operator()(const term_instance& x) const;
    };
}
