#pragma once
#include "CadicalWrapper.h"
#include <stack>

struct term;
struct term_instance;
struct SimpleADTSolver;
struct subterm_hint;
struct propagator_base;

struct raw_term {
    int FuncID;
    const pvector<term> Args;

    raw_term(int funcId, pvector<term> args) : FuncID(funcId), Args(std::move(args)) {
    }

    bool operator==(const raw_term& other) const {
        if (FuncID != other.FuncID || Args.size() != other.Args.size())
            return false;
        for (unsigned i = 0; i < Args.size(); i++)
            if (Args[i] != other.Args[i])
                return false;
        return true;
    }
    bool operator!=(const raw_term& other) const {
        return !this->operator==(other);
    }
};

namespace std {
    template <>
    struct hash<raw_term> {
        size_t operator()(const raw_term& x) const;
    };
}

struct RawTermWrapper {
    const raw_term* obj;

    RawTermWrapper(const raw_term* obj) : obj(obj) { }

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
            static hash<raw_term> hash;
            return hash(*x.obj);
        }
    };
}

struct term_instance;

class term : public raw_term {

    mutable vector<term_instance*> instances;

public:
    const unsigned HashID;
    const bool Ground;
    SimpleADTSolver& Solver;

    unsigned getSolverId() const;

    bool is_var() const { return FuncID < 0; }
    bool is_const() const { return FuncID >= 0; }

    bool operator==(const term& other) const {
        return getSolverId() == other.getSolverId() && HashID == other.HashID;
    }

    bool operator!=(const term& other) const {
        return !this->operator==(other);
    }

    term(int funcId, pvector<term> args, SimpleADTSolver& solver, unsigned hashId);

    term(const term&) = delete;

    ~term();

    void reset();

    term_instance* GetInstance(unsigned cpy) const;

    bool SeemsPossiblyUnifiable(term* rhs, subterm_hint& hint);

    int compare_to(const term* other) const {
        return this == other ? 0 : (HashID < other->HashID ? -1 : HashID > other->HashID ? 1 : 0);
    }

    string to_string() const;

    string PrettyPrint(unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const;
};

namespace std {
    template <>
    struct hash<term> {
        size_t operator()(const term& x) const;
    };
}

struct Justification {
    virtual void AddJustification(SimpleADTSolver* adtSolver, vector<literal>& just) = 0;
    virtual bool is_tautology() const = 0;
    virtual string to_string() const = 0;
};

struct LiteralJustification : public Justification {

    literal lit;

    LiteralJustification(literal lit) : lit(lit) { }

    void AddJustification(SimpleADTSolver* adtSolver, vector<literal>& just) override {
        just.push_back(lit);
    }

    bool is_tautology() const override { return lit->is_true(); }

    string to_string() const override {
        return lit->to_string();
    }
};

class EqualityJustification : public Justification {
    term_instance* LHS;
    term_instance* RHS;

public:
    EqualityJustification(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) { }

    void AddJustification(SimpleADTSolver* adtSolver, vector<literal>& just) override;

    bool is_tautology() const override { return LHS == RHS; }

    string to_string() const override;
};

struct CheckPosition {
    int ArgIdx;
    term_instance* LHS;
    term_instance* RHS;

    CheckPosition(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) {}

    string to_string() const;
};

struct Lazy {
    vector<Justification*> Justifications;
    stack<CheckPosition> Prev;
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;
    bool Solved = false;

    Lazy() = default;
    Lazy(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) { }
};

class lessThan {
public:
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;

    lessThan() = default;
    lessThan(term_instance* lhs, term_instance* rhs);

    bool operator==(const lessThan& other) const {
        return LHS == other.LHS && RHS == other.RHS;
    }

    bool operator!=(const lessThan& other) const {
        return !this->operator==(other);
    }

    string to_string() const;
};

class equality {

public:
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;
    vector<Justification*> just;

    equality() = default;
    equality(term_instance* lhs, term_instance* rhs, vector<Justification*> just);

    term_instance* GetOther(term_instance* lhsOrRhs) {
        assert(LHS == lhsOrRhs || RHS == lhsOrRhs);
        return LHS == lhsOrRhs ? RHS : LHS;
    }

    bool operator==(const equality& other) const {
        return LHS == other.LHS && RHS == other.RHS;
    }

    bool operator!=(const equality& other) const {
        return !this->operator==(other);
    }

    string to_string() const;
};

namespace std {
    template <>
    struct hash<equality> {
        size_t operator()(const equality& x) const;
    };
    template <>
    struct hash<lessThan> {
        size_t operator()(const lessThan& x) const;
    };
}

struct term_instance {
    // ast
    const term* t;
    const unsigned cpyIdx;

    // enode
    term_instance* parent;
    vector<equality> actual_connections;
    unsigned cnt = 1;

    // PO node
    vector<tuple<term_instance*, bool, vector<Justification*>>> greater;
    vector<tuple<term_instance*, bool, vector<Justification*>>> smaller;

    // watches
    vector<Lazy*> diseq_watches;
    vector<tuple<term_instance*, term_instance*, bool, literal>> smaller_watches;

    bool is_root() const {
        return parent == this;
    }

private:
    term_instance(const term* term, unsigned cpyIdx) : t(term), cpyIdx(cpyIdx), parent(this) { }

public:
    static term_instance* NewInstance(const term* term, unsigned copy) {
        return new term_instance(term, copy);
    }

    term_instance* FindRootQuick(propagator_base& propagator);

    inline bool operator==(const term_instance& other) const {
        return *t == *other.t && cpyIdx == other.cpyIdx;
    }

    inline bool operator!=(const term_instance& other) const {
        return !this->operator==(other);
    }

    int compare_to(const term_instance* other) {
        if (this == other)
            return 0;
        int ret = t->compare_to(other->t);
        return ret != 0 ? ret : (cpyIdx < other->cpyIdx ? -1 : cpyIdx > other->cpyIdx ? 1 : 0);
    }

    string to_string() const {
        if (t->Ground)
            return t->to_string();
        return t->to_string() + "#" + std::to_string(cpyIdx);
    }
};

namespace std {
    template <>
    struct hash<term_instance> {
        size_t operator()(const term_instance& x) const;
    };
    template <>
    struct hash<term_instance*> {
        size_t operator()(const term_instance* x) const {
            return (size_t)x;
        }
    };
    template <>
    struct equal_to<term_instance*> {
        bool operator()(const term_instance* x, const term_instance* y) const {
            return *x == *y;
        }
    };
}
