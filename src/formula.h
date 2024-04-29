#pragma once

#include "utils.h"

#ifndef NDEBUG
extern std::unordered_map<unsigned, std::string> names;
inline void reset_names() {
    names.clear();
}
#define OPT(X) X
#else
#define OPT(X)
#endif

class z3_propagator;
class propagator_base;
class formula_term;
class true_term;
class false_term;
class literal_term;
class not_term;
class and_term;
class or_term;

using literal = literal_term*;
using formula = formula_term*;

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
    friend class propagator_base;
    propagator_base* propagator;
    true_term* trueTerm;
    false_term* falseTerm;

    std::vector<formula_term*> id_to_formula;
    std::vector<literal> cadical_to_formula;
    std::vector<literal> neg_cadical_to_formula;

    std::unordered_map<formula_term*, formula_term*> not_cache;
    std::unordered_map<std::vector<formula_term*>, and_term*> and_cache;
    std::unordered_map<std::vector<formula_term*>, or_term*> or_cache;

public:

    true_term* mk_true() const;

    false_term* mk_false() const;

    literal mk_lit(unsigned v, bool neg);

    literal mk_lit(signed v);

    literal mk_not(literal c);
    formula_term* mk_not(formula_term* c);

    formula_term* mk_or(std::vector<formula_term*> c, bool positive = false);
    formula_term* mk_and(std::vector<formula_term*> c, bool positive = false);

#ifndef NDEBUG
    formula_term* mk_or_slow(const std::vector<literal>& c){
        return mk_or(std::vector<formula_term*>(c.begin(), c.end()));
    }

    formula_term* mk_and_slow(const std::vector<literal>& c) {
        return mk_and(std::vector<formula_term*>(c.begin(), c.end()));
    }
#endif

    formula_manager(propagator_base* propagator);
    ~formula_manager();

    void register_formula(formula_term* term);
};

struct clause_instance;

class formula_term {

    const unsigned ast_id;
    tri_state final_interpretation = undef;

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

    struct connection_tseitin {
        literal sideCondition;
        clause_instance* c1;
        clause_instance* c2;
    };

    vector<connection_tseitin> connections; // If true: The two clauses are linked (because of root simplifications, a single formula can link more two clauses)

    virtual ~formula_term() = default;

    virtual bool is_literal() const {
        return false;
    }

    inline unsigned get_ast_id() const {
        return ast_id;
    }

    inline int get_var_id() const {
        return var_id;
    }

    inline tri_state get_fixed() const {
        return final_interpretation;
    }

    inline void fix(bool t) {
        assert(final_interpretation == undef);
        final_interpretation = t ? sat : unsat;
    }

    inline bool is_true() const {
        return final_interpretation == sat;
    }

    inline bool is_false() const {
        return final_interpretation == unsat;
    }

    virtual std::string to_string() const = 0;

    // first:  0 -> just create a new variable and return it
    // first:  1 -> inline the variable positively
    // first: -1 -> inline the variable negatively
    virtual const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) = 0;

    virtual z3::expr get_z3(z3_propagator& propagator) = 0;

    virtual formula_term* negate() = 0;
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

    bool is_literal() const final {
        return true;
    }

    int get_lit() const {
        return var_id;
    }

    std::string to_string() const override {
        return name;
    }

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) override {
        return this;
    }

    z3::expr get_z3(z3_propagator& propagator) override;

    formula_term* negate() override {
        return manager.mk_lit(-var_id);
    }
};

struct false_term : public literal_term {
    false_term(formula_manager& m) : literal_term(m, 0, true) {}

    std::string to_string() const final { return "false"; }

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) final {
        return nullptr;
    }

    z3::expr get_z3(z3_propagator& propagator) final;

    formula_term* negate() final {
        return (formula_term*)manager.mk_true();
    }
};

struct true_term : public literal_term {
    true_term(formula_manager& m) : literal_term(m, 0, false) {}

    std::string to_string() const final { return "true"; }

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) final {
        return nullptr;
    }

    z3::expr get_z3(z3_propagator& propagator) final;

    formula_term* negate() final {
        return (formula_term*)manager.mk_false();
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

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) override;

    z3::expr get_z3(z3_propagator& propagator) final;

    formula_term* negate() final {
        return t;
    }
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

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) override;

    z3::expr get_z3(z3_propagator& propagator) final;

    formula_term* negate() final {
        vector<formula_term*> negated;
        negated.reserve(args.size());
        for (auto* arg : args) {
            negated.push_back(arg->negate());
        }
        return manager.mk_or(negated);
    }
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

    const literal get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) override;

    z3::expr get_z3(z3_propagator& propagator) final;

    formula_term* negate() final {
        vector<formula_term*> negated;
        negated.reserve(args.size());
        for (auto* arg : args) {
            negated.push_back(arg->negate());
        }
        return manager.mk_and(negated);
    }
};
