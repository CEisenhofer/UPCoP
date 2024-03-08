#pragma once

#include "cadical.hpp"
#include "utils.h"

#include <iostream>

#ifndef NDEBUG
extern std::unordered_map<unsigned, std::string> names;
inline void reset_names() {
    names.clear();
}
#ifndef NOLOG
#define Log(s) do { std::cout << s; } while (false)
#define LogN(s) Log(s << std::endl)
#else
#define Log(s) do { } while (false)
#define LogN(s) Log(s)
#endif
#define OPT(X) X
#else
inline void reset_names() {
}
#define Log(s) do { } while (false)
#define LogN(s) Log(s)
#define OPT(X)
#endif

class CaDiCal_propagator;
class formula_term;
class true_term;
class false_term;
class literal_term;
class not_term;
class and_term;
class or_term;

typedef literal_term* literal;
#define literal_to_string(X) (X)->to_string()
#define literal_to_atom(X) mk_lit(abs((X)->get_lit()))
#define literal_to_polarity(X) ((bool)((X)->get_lit() > 0))
#define literal_to_negate(X) mk_lit(-((X)->get_lit()))
typedef formula_term* formula;

namespace std {
    template<>
    struct hash<literal_term*> {
        size_t operator()(const literal_term* const x) const;
    };

    template<>
    struct equal_to<literal_term*> {
        bool operator()(const literal_term* const x, const literal_term* const y) const;
    };

    template<>
    struct hash<std::vector<formula_term*>> {
        size_t operator()(const std::vector<formula_term*>& x) const;
    };

    template<>
    struct equal_to<std::vector<formula_term*>> {
        bool operator()(const std::vector<formula_term*>& x, const std::vector<formula_term*>& y) const;
    };
}

class formula_manager {
    friend class formula_term;
    friend class CaDiCal_propagator;
    CaDiCal_propagator* propagator;
    true_term* trueTerm;
    false_term* falseTerm;

    std::vector<formula_term*> id_to_formula;
    std::vector<literal_term*> cadical_to_formula;
    std::vector<literal_term*> neg_cadical_to_formula;

    std::unordered_map<formula_term*, not_term*> not_cache;
    std::unordered_map<std::vector<formula_term*>, and_term*> and_cache;
    std::unordered_map<std::vector<formula_term*>, or_term*> or_cache;

public:

    true_term* mk_true() const;

    false_term* mk_false() const;

    literal_term* mk_lit(unsigned v, bool neg);

    literal_term* mk_lit(signed v);

    literal_term* mk_not(literal_term* c);
    formula_term* mk_not(formula_term* c);

    formula_term* mk_or(std::vector<formula_term*> c, bool positive = false);

    formula_term* mk_and(std::vector<formula_term*> c, bool positive = false);

#ifndef NDEBUG
    formula_term* mk_or_slow(const std::vector<literal_term*>& c){
        return mk_or(std::vector<formula_term*>(c.begin(), c.end()));
    }

    formula_term* mk_and_slow(const std::vector<literal_term*>& c) {
        return mk_and(std::vector<formula_term*>(c.begin(), c.end()));
    }
#endif

    formula_manager(CaDiCal_propagator* propagator);
    ~formula_manager();

    bool is_true(const formula_term* t) const {
        return t == (formula_term*)trueTerm;
    }

    bool is_false(const formula_term* t) const {
        return t == (formula_term*)falseTerm;
    }

    void register_formula(formula_term* term);
};

#ifndef PUSH_POP
constexpr bool active = true;
#endif

class formula_term {

    const unsigned ast_id;

protected:

#ifdef PUSH_POP
    bool active = false;
#endif

    formula_manager& manager;
    int var_id = 0;

    explicit formula_term(formula_manager& manager) : ast_id(manager.id_to_formula.size()), manager(manager) {
        manager.register_formula(this);
    }

public:

    virtual ~formula_term() = default;

    virtual bool is_literal() const {
        return false;
    }

    unsigned get_ast_id() const {
        return ast_id;
    }

    int get_var_id() const {
        return var_id;
    }

    bool is_true() const {
        return manager.is_true(this);
    }

    bool is_false() const {
        return manager.is_false(this);
    }

    virtual std::string to_string() const = 0;

    // first:  0 -> just create a new variable and return it
    // first:  1 -> inline the variable positively
    // first: -1 -> inline the variable negatively
    virtual const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) = 0;
};

class literal_term : public formula_term {
    const std::string name;

public:

    literal_term(formula_manager& m, unsigned l, bool neg) : formula_term(m)
#ifndef NDEBUG
                                                             , name((neg ? "!" : "") + names.at(l))
#endif
                                                             {
        var_id = (signed) l * (neg ? -1 : 1);
    }

    literal_term(formula_manager& m, signed l) : formula_term(m)
#ifndef NDEBUG
                                                            , name((l < 0 ? "!" : "") + names.at(abs(l)))
#endif
                                                            {
        var_id = l;
    }

public:

    bool is_literal() const final {
        return true;
    }

    int get_lit() const {
        return var_id;
    }

    std::string to_string() const override {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

class false_term : public literal_term {
public:
    false_term(formula_manager& m) : literal_term(m, 0, true) {}

    std::string to_string() const final { return "false"; }

    const literal_term*
    get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) final {
        return nullptr;
    }
};

class true_term : public literal_term {
public:
    true_term(formula_manager& m) : literal_term(m, 0, false) {}

    std::string to_string() const final { return "true"; }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) final {
        return nullptr;
    }
};

class not_term : public formula_term {
    formula_term* t;
    const std::string name;

public:

    explicit not_term(formula_manager& m, formula_term* t) : formula_term(m), t(t), name("!" + t->to_string()) {}

    std::string to_string() const final {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

class complex_term : public formula_term {

protected:

    const std::vector<formula_term*> args;
    const bool positive;

public:

    bool is_positive() const {
        return positive;
    }

    const std::vector<formula_term*>& get_args() const {
        return args;
    }

    // TODO: Check if positive really makes a difference
    explicit complex_term(formula_manager& m, std::vector<formula_term*> args, bool positive) :
                                                                formula_term(m), args(std::move(args)), positive(positive) {
        assert(this->args.size() > 1);
    }
};

class and_term : public complex_term {
    const std::string name;

public:
    explicit and_term(formula_manager& m, std::vector<formula_term*> args, bool positive) :
                                                                complex_term(m, std::move(args), positive),
                                                                name(string_join(this->args, " && ")) {
    }

    std::string to_string() const final {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

class or_term : public complex_term {
    const std::string name;

public:
    explicit or_term(formula_manager& m, std::vector<formula_term*> args, bool positive) :
                                                               complex_term(m, std::move(args), positive), name(string_join(this->args, " || ")) {
    }

    std::string to_string() const final {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

enum tri_state : unsigned char {
    undef = 0,
    sat = 1,
    unsat = 2,
};

typedef std::function<void()> action;

class CaDiCal_propagator : public CaDiCaL::ExternalPropagator {
    friend class formula_manager;

protected:
    std::vector<action> undo_stack;

#ifdef DIMACS
    std::stringstream dimacs;
#endif

private:
    int var_cnt = 0;
    std::vector<unsigned> undo_stack_limit;

    unsigned pending_hard_propagations_idx = 0;
    unsigned hard_propagation_read_idx = 0;
    std::vector<std::vector<int>> pending_hard_propagations;

    std::vector<unsigned> soft_propagation_limit;
    std::vector<unsigned> soft_propagation_undo;
    std::vector<std::pair<std::vector<int>, int>> pending_soft_propagations;
    std::vector<std::vector<int>> soft_justifications;
    unsigned soft_propagation_read_idx = 0;

    std::vector<tri_state> interpretation;

    // for persistent propagation
    std::unordered_set<std::vector<int>> prev_propagations;

    unsigned literal_to_idx(int lit) const {
        return 2 * abs(lit) + (unsigned)(lit < 0);
    }

protected:
    bool is_conflict_flag = false;

public:

    bool is_conflict() const {
        return is_conflict_flag;
    }

    CaDiCaL::Solver* solver = nullptr;
    formula_manager m;

    inline void add_undo(const action& action) {
        assert(solver->state() == CaDiCaL::SOLVING);
        undo_stack.push_back(action);
    }

    tri_state check() {
        switch (solver->solve()) {
            case 10:
                return sat;
            case 20:
                return unsat;
            default:
                return undef;
        }
    }

    unsigned vars() {
        return (unsigned)solver->vars();
    }

#ifdef DIMACS
    string get_dimacs() {
        string clauses = dimacs.str();
        unsigned cnt = 0;
        for (char c : clauses) {
            cnt += (unsigned)(c == '\n');
        }
        string ret = "p cnf " + std::to_string(vars()) + " " + to_string(cnt - 1) + "\n";
        ret += dimacs.str();
        return ret;
    }
#endif

#ifndef NDEBUG
    void output_literals(const std::vector<literal>& lit) const;
#endif

    void propagate_conflict(const std::vector<literal>& just);

    bool hard_propagate(const std::vector<literal>& just, formula prop);

    bool soft_propagate(const std::vector<literal>& just, literal prop);

protected:

    CaDiCal_propagator() : m(this) {
        init_solver();
    }

    bool get_value(literal v, bool& value) const {
        tri_state val = interpretation[abs(v->get_lit()) - 1];
        if (val == undef)
            return false;
        value = val == sat;
        return true;
    }

    bool has_value(literal v) const {
        return interpretation[abs(v->get_lit()) - 1] != undef;
    }

    int new_var_raw() {
        int newId = ++var_cnt;
        soft_justifications.emplace_back();
        soft_justifications.emplace_back();
        assert(2 * var_cnt == soft_justifications.size());
        interpretation.push_back(undef);
        assert(var_cnt == interpretation.size());
        return newId;
    }

    int new_observed_var_raw() {
        signed newId = new_var_raw();
        solver->add_observed_var(newId);
        return newId;
    }

    void init_solver();

public:
#ifndef NDEBUG

    inline int new_observed_var(const std::string& name) {
        int id = new_observed_var_raw();
        names.insert(std::make_pair(id, name));
        return id;
    }

    inline int new_var() {
        return new_var_raw();
    }

#else
    int new_var() {
        return new_var_raw();
    }

    int new_observed_var() {
        return new_observed_var_raw();
    }
#endif

    inline void observe_again(int var_id) {
        solver->add_observed_var(var_id);
    }

    inline void observe_remove(int var_id) {
        // solver->remove_observed_var(var_id);
        // solver->melt(var_id);
    }

protected:

    virtual void fixed(literal lit, bool value) = 0;

    void notify_assignment(const vector<int>& lits) final;

    void notify_new_decision_level() final;

    void notify_backtrack(size_t new_level) final;

    void pop_to_root() {
        if (undo_stack_limit.empty())
            return;
        notify_backtrack(0);
    }

    virtual void final() = 0;

    bool cb_check_found_model(const std::vector<int>& model) final;

    int cb_propagate() final;

    int cb_add_reason_clause_lit(int propagated_lit) final;

protected:

    bool cb_has_external_clause(bool& is_forgettable) final;

    int cb_add_external_clause_lit() final;

    int cb_decide() final;

    virtual literal decide() = 0;
};
