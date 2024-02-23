#pragma once

#include "cadical.hpp"
#include "utils.h"

#ifndef NDEBUG
extern std::unordered_map<unsigned, std::string> names;
#define Log(s) do { std::cout << s; } while (false)
#define LogN(s) Log(s << std::endl)
#else
#define Log(s) do { } while (false)
#define LogN(s) Log(s)
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
#define literal_to_polarity(X) ((X)->get_lit() > 0)
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

    formula_term* mk_or(std::vector<formula_term*> c);

    formula_term* mk_and(std::vector<formula_term*> c);

#ifndef NDEBUG
    formula_term* mk_or_slow(const std::vector<literal_term*>& c){
        return mk_or(std::vector<formula_term*>(c.begin(), c.end()));
    }

    formula_term* mk_and_slow(const std::vector<literal_term*>& c) {
        return mk_and(std::vector<formula_term*>(c.begin(), c.end()));
    }
#endif

    formula_manager();
    ~formula_manager();

    bool is_true(const formula_term* t) const {
        return t == (formula_term*)trueTerm;
    }

    bool is_false(const formula_term* t) const {
        return t == (formula_term*)falseTerm;
    }
};

class formula_term {

    const unsigned ast_id;

protected:

    formula_manager& manager;
    int var_id = 0;

    explicit formula_term(formula_manager& manager) : ast_id(manager.id_to_formula.size()), manager(manager) {
        manager.id_to_formula.push_back(this);
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

    static std::string string_join(const std::vector<formula_term*>& args, const std::string& sep) {
        assert(!args.empty());
        if (args.size() == 1)
            return args[0]->to_string();
        std::stringstream sb;
        sb << "(" << args[0]->to_string();
        for (unsigned i = 1; i < args.size(); i++) {
            sb << sep << args[i]->to_string();
        }
        sb << ")";
        return sb.str();
    }
};

class literal_term : public formula_term {
    const std::string name;

public:

    literal_term(formula_manager& m, unsigned l, bool neg) : formula_term(m),
                                                             name((neg ? "!" : "") + names.at(l)) {
        var_id = (signed) l * (neg ? -1 : 1);
    }

    literal_term(formula_manager& m, signed l) : formula_term(m), name((l < 0 ? "!" : "") + names.at(abs(l))) {
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

public:

    explicit complex_term(formula_manager& m, std::vector<formula_term*> args) : formula_term(m), args(std::move(args)) {
        assert(this->args.size() > 1);
    }
};

class and_term : public complex_term {
    const std::string name;

public:
    explicit and_term(formula_manager& m, std::vector<formula_term*> args) : complex_term(m, std::move(args)), name(string_join(this->args, " && ")) {
    }

    std::string to_string() const final {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

class or_term : public complex_term {
    const std::string name;

public:
    explicit or_term(formula_manager& m, std::vector<formula_term*> args) : complex_term(m, std::move(args)), name(string_join(this->args, " || ")) {
    }

    std::string to_string() const final {
        return name;
    }

    const literal_term* get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) override;
};

enum tri_state : unsigned char {
    sat, unsat, undef
};

typedef std::function<void()> action;

struct literal_hash {
    size_t operator()(const literal& x) const {
        return abs(x->get_lit());
    }
};

struct literal_eq {
    bool operator()(const literal& x, const literal& y) const {
        return abs(x->get_lit()) == abs(y->get_lit());
    }
};

class CaDiCal_propagator : public CaDiCaL::ExternalPropagator {

protected:
    std::vector<action> undoStack;

private:
    std::vector<unsigned> undoStackSize;

    unsigned propagationIdx = 0;
    unsigned propagationReadIdx = 0;
    std::vector<std::vector<int>> propagations;

    std::unordered_map<literal, bool, literal_hash, literal_eq> interpretation;


    // for persistent propagation
    std::unordered_set<std::vector<int>> prev_propagations;

protected:
    bool is_conflict_flag = false;

public:

    bool is_conflict() const {
        return is_conflict_flag;
    }

    CaDiCaL::Solver* solver = nullptr;
    formula_manager m;

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

    bool val(int v) {
        return solver->val(abs(v)) > 0;
    }

    void propagate_conflict(std::vector<literal> just);

    void propagate(const std::vector<literal>& just, formula prop);

protected:

    CaDiCal_propagator() {
        reinit_solver();
    }

    unsigned decision_lvl() const {
        return undoStackSize.size();
    }

    bool get_value(literal v, bool& value) const {
        auto it = interpretation.find(v);
        if (it == interpretation.end())
            return false;
        value = it->second;
        return true;
    }

    int new_var_raw() {
        signed newId = (signed) vars() + 1;
        // solver->add_observed_var(newId);
        return newId;
    }

    int new_observed_var_raw() {
        signed newId = new_var_raw();
        solver->add_observed_var(newId);
        return newId;
    }

    void reinit_solver();
    virtual void reinit_solver2() = 0;

public:
#ifndef NDEBUG

    int new_var(const std::string& name) {
        return new_var_raw(); // We do not really care about this variable...
    }

    int new_observed_var(const std::string& name) {
        int id = new_observed_var_raw();
        names.insert(std::make_pair(id, name));
        return id;
    }

#else
#define new_var(X) new_var_raw()
#define new_observed_var(X) new_obsered_var_raw()
#endif

protected:

    virtual void fixed(literal lit, bool value) = 0;

    void notify_assignment(const vector<int>& lits) override;

    void notify_new_decision_level() override;

    void notify_backtrack(size_t new_level) override;

    virtual void final() = 0;

    bool cb_check_found_model(const std::vector<int>& model) override;

    int cb_propagate() override {
        return 0;
    }

    bool cb_has_external_clause(bool& is_forgettable) override;

    int cb_add_external_clause_lit() override;
};
