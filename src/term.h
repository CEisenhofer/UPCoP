#pragma once
#include "CadicalWrapper.h"
#include <stack>

struct term;
struct term_instance;
struct simple_adt_solver;
struct subterm_hint;
struct propagator_base;
struct matrix_propagator;
struct indexed_clause;
struct clause_instance;

struct raw_term {
    int FuncID;
    const vector<const term*> Args;

    raw_term(int funcId, vector<const term*> args) : FuncID(funcId), Args(std::move(args)) {
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

    friend class simple_adt_solver;

    mutable vector<term_instance*> instances;

    const unsigned ast_id;
    const indexed_clause* origin_clause; // Might point to uninitialized during input parsing

public:

    simple_adt_solver& Solver;

#ifndef NDEBUG
private:
    const string name;

public:
#endif

    unsigned solver_id() const;
    const indexed_clause* clause() const {
        return origin_clause;
    }

    bool is_var() const { return FuncID < 0; }
    bool is_const() const { return FuncID >= 0; }

    bool is_ground() const {
        return origin_clause == nullptr;
    }

    unsigned id() const {
        return ast_id;
    }

    bool operator==(const term& other) const {
        return solver_id() == other.solver_id() && ast_id == other.ast_id && origin_clause == other.origin_clause;
    }

    bool operator!=(const term& other) const {
        return !this->operator==(other);
    }

    term(int funcId, vector<const term*> args, simple_adt_solver& solver, unsigned hashId, const indexed_clause* clause);

    term(const term&) = delete;

    ~term();

    void reset();

    term_instance* get_instance(unsigned cpy, matrix_propagator& propagator) const;

    bool SeemsPossiblyUnifiable(const term* rhs, subterm_hint& hint) const;

    int compare_to(const term* other) const {
        return this == other ? 0 : (id() < other->id() ? -1 : id() > other->id() ? 1 : 0);
    }

    string to_string() const;

    string pretty_print(unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const;
};

namespace std {
    template <>
    struct hash<term> {
        size_t operator()(const term& x) const;
    };
}

struct justification {

    vector<literal> litJust;
    vector<pair<term_instance*, term_instance*>> eqJust;

    void add_literal(literal lit) {
        litJust.push_back(lit);
    }

    void add_literals(const std::vector<literal>& lit) {
        add_range(litJust, lit);
    }

    void remove_literal() {
        litJust.pop_back();
    }

    void add_equality(term_instance* lhs, term_instance* rhs) {
        // this is not an equivalence class; order does not matter
        eqJust.emplace_back(lhs, rhs);
    }

    void remove_equality() {
        eqJust.pop_back();
    }

    void add(const justification& other) {
        add_range(litJust, other.litJust);
        add_range(eqJust, other.eqJust);
    }

    string to_string() const;

    void resolve_justification(simple_adt_solver* adtSolver, vector<literal>& just,
                               unordered_map<term_instance*, unsigned>& termInstance, vector<unsigned>& parent) const;

    void resolve_justification(simple_adt_solver* adtSolver, vector<literal>& just) const;

    bool empty() const {
        return litJust.empty() && eqJust.empty();
    }
};

struct position {
    int argIdx;
    term_instance* lhs;
    term_instance* rhs;

    position(term_instance* lhs, term_instance* rhs) : argIdx(0), lhs(lhs), rhs(rhs) {}

#ifndef NDEBUG
    string to_string() const;
#endif
};

struct Lazy {
    justification just;
    stack<position> prev;
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;
    bool Solved = false;

    Lazy() = default;
    Lazy(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) { }
};

struct less_than {
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;

    less_than() = default;
    less_than(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) { }

    bool operator==(const less_than& other) const {
        return LHS == other.LHS && RHS == other.RHS;
    }

    bool operator!=(const less_than& other) const {
        return !this->operator==(other);
    }

#ifndef NDEBUG
    string to_string() const;
#endif
};

struct equality {
    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;
    justification just;

    equality() = default;
    equality(term_instance* lhs, term_instance* rhs, justification just);
    equality(term_instance* lhs, term_instance* rhs) : equality(lhs, rhs, {}) { }

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

#ifndef NDEBUG
    string to_string() const;
#endif
};

struct disequality {

    term_instance* LHS = nullptr;
    term_instance* RHS = nullptr;
    literal just;

    disequality() = default;
    disequality(term_instance* lhs, term_instance* rhs, literal just);

#ifndef NDEBUG
    string to_string() const;
#endif
};

namespace std {
    template <>
    struct hash<equality> {
        size_t operator()(const equality& x) const;
    };
    template <>
    struct hash<less_than> {
        size_t operator()(const less_than& x) const;
    };
}

struct term_instance {

    // ast
    const term* const t;
    clause_instance* const origin;

    // enode
    term_instance* parent;
    vector<equality> actual_connections;
    term_instance* next_sibling;
    term_instance* prev_sibling;
    unsigned cnt = 1;

    unsigned marked = 0;

    // PO node
    vector<pair<term_instance*, literal>> smaller;

    // watches
    //vector<equality> eq_split_watches;
    //unsigned eq_split_watches_idx = 0;
    vector<disequality> diseq_split_watches;
    unsigned diseq_split_watches_idx = 0;
    vector<Lazy*> diseq_watches;
    vector<tuple<term_instance*, term_instance*, literal>> smaller_watches;
    unsigned smaller_watches_idx = 0;

#ifndef NDEBUG
    const string name;
#endif

    bool is_root() const {
        return parent == this;
    }

private:
    term_instance(const term* term, clause_instance* origin) :
                                                                t(term), origin(origin),
                                                                parent(this), prev_sibling(this), next_sibling(this)
#ifndef NDEBUG
                                                                , name(to_string())
#endif
                                                                { }

public:

    term_instance(const term_instance&) = delete;
    term_instance& operator=(const term_instance&) = delete;

    static term_instance* new_instance(const term* term, clause_instance* origin) {
        return new term_instance(term, origin);
    }

    inline term_instance* get_arg(unsigned arg, matrix_propagator& propagator) {
        return t->Args[arg]->get_instance(cpy_idx(), propagator);
    }

    unsigned cpy_idx() const;

    term_instance* find_root(propagator_base& propagator);

    inline bool operator==(const term_instance& other) const {
        bool ret = *t == *other.t && cpy_idx() == other.cpy_idx();
        assert (!ret || origin == other.origin);
        return ret;
    }

    inline bool operator!=(const term_instance& other) const {
        return !this->operator==(other);
    }

    int compare_to(const term_instance* other) {
        if (this == other)
            return 0;
        int ret = t->compare_to(other->t);
        return ret != 0 ? ret : (cpy_idx() < other->cpy_idx() ? -1 : cpy_idx() > other->cpy_idx() ? 1 : 0);
    }

    string to_string() const {
        if (t->is_ground())
            return t->to_string();
        return t->to_string() + "#" + std::to_string(cpy_idx());
    }

    string pretty_print(unordered_map<term_instance*, string>* prettyNames) const {
        return t->pretty_print(cpy_idx(), prettyNames);
    }

    z3::expr to_z3(matrix_propagator& propagator, z3::context& context, unordered_map<term_instance*, optional<z3::expr>>& map, vector<term_instance*>& terms);

    const term* fully_expand(matrix_propagator& propagator);
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