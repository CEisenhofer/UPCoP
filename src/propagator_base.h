#pragma once

#include "adt_solver.h"
#include "CLIParser.h"
#include "cnf.h"
#include "ground_literal.h"
#include "CadicalWrapper.h"
#include "Z3Wrapper.h"
#include <random>

class subterm_hint;

namespace std {
    template<typename T>
    struct hash<std::pair<T, T>> {
        inline size_t operator()(const pair<T, T>& x) const {
            static std::hash<T> hash;
            return hash(x.first) * 31 + hash(x.second);
        }
    };
    template<typename T>
    struct equal_to<std::pair<T, T>> {
        inline size_t operator()(const pair<T, T>& x, const pair<T, T>& y) const {
            return x.first == y.first && x.second == y.second;
        }
    };
}

struct propagator_base {

    mutable std::default_random_engine generator;
    mutable std::uniform_int_distribution<unsigned> distribution;

    z3_propagator* const z3Propagator;
    CaDiCal_propagator* const cadicalPropagator;

protected:

    ProgParams& progParams;
    const cnf<indexed_clause*>& matrix;

    std::vector<action> undo_stack;

    bool is_conflict_flag = false;

public:

    complex_adt_solver& term_solver;
    formula_manager& m;

    propagator_base(propagator_base&) = delete;
    propagator_base& operator=(propagator_base&) = delete;

    // [min, max)
    unsigned get_random(unsigned min, unsigned max) const;

    inline bool is_adt_split() const {
        return progParams.satSplit;
    }

    inline bool is_smt() const {
        return progParams.smt;
    }

    CaDiCal_propagator* get_cadical_propagator() const {
        return cadicalPropagator;
    }

    z3_propagator* get_z3_propagator() const {
        return z3Propagator;
    }

    propagator_base(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned timeLeft);
    virtual ~propagator_base();


    inline void add_undo(const action& action) {
        undo_stack.push_back(action);
    }

    inline bool is_conflict() const {
        return is_conflict_flag;
    }

    inline void set_conflict() {
        assert(!is_conflict_flag);
        is_conflict_flag = true;
    }

    inline void clear_conflict() {
        is_conflict_flag = false;
    }

#ifndef NDEBUG

    inline int new_observed_var(const std::string& name) {
        // phase -- TODO!!!
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->new_observed_var(name);
        return z3Propagator->new_observed_var(name);
    }

    inline int new_var(const std::string& name) {
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->new_var(name);
        assert(false);
        throw solving_exception("Z3 does not require generating non-observed variables.");
    }

#else

    int new_observed_var() {
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->new_observed_var();
        return z3Propagator->new_observed_var();
    }

    int new_var() {
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->new_var();
        throw solving_exception("Z3 does not require generating non-observed variables.");
    }
#endif

    inline bool is_skip(literal v) const {
        return cadicalPropagator != nullptr && cadicalPropagator->is_skip(v);
    }

    inline bool has_value(literal v) const {
        return cadicalPropagator != nullptr ? cadicalPropagator->has_value(v) : z3Propagator->has_value(v);
    }

    inline void assume(literal v) const {
        if (cadicalPropagator != nullptr)
            cadicalPropagator->assume(v);
        else
            z3Propagator->assume(v);
    }

    inline void add_assertion(literal v) const {
        if (cadicalPropagator != nullptr)
            cadicalPropagator->add_assertion(v);
        else
            z3Propagator->add_assertion(v);
    }

    inline void add_assertion(vector<literal> v) const {
        if (cadicalPropagator != nullptr)
            cadicalPropagator->add_assertion(std::move(v));
        else
            z3Propagator->add_assertion(std::move(v));
    }

    inline bool failed(literal v) const {
        return cadicalPropagator != nullptr ? cadicalPropagator->failed(v) : z3Propagator->failed(v);
    }

    inline bool get_value(literal v, bool& value) const {
        return cadicalPropagator != nullptr ? cadicalPropagator->get_value(v, value) : z3Propagator->get_value(v, value);
    }

    inline tri_state check() const {
        return cadicalPropagator != nullptr ? cadicalPropagator->check() : z3Propagator->check();
    }

    inline void propagate_conflict(const justification& just) const {
        if (cadicalPropagator != nullptr)
            cadicalPropagator->propagate_conflict(just);
        else
            z3Propagator->propagate_conflict(just);
    }

    inline bool hard_propagate(const justification& just, formula prop) const {
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->hard_propagate(just, prop);
        return z3Propagator->propagate(just, (literal)prop);
    }

    inline bool soft_propagate(const justification& just, literal prop) const {
        if (cadicalPropagator != nullptr)
            return cadicalPropagator->soft_propagate(just, prop);
        return z3Propagator->propagate(just, prop);
    }

    static string clause_to_string(const vector<ground_literal>& ground, unordered_map<term_instance*, string>* prettyNames);

    static string pretty_print_literal(const fo_literal* l, unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames);

    static string pretty_print_literal(const ground_literal& l, unordered_map<term_instance*, string>* prettyNames) {
        return pretty_print_literal(l.lit, l.copyIdx, prettyNames);
    }

    virtual void fixed(literal e, bool value) = 0;
    virtual void final() = 0;

    inline vector<action>& get_undo() {
        return undo_stack;

    }

protected:

    clause_instance* create_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector);

    template<typename T>
    void Shuffle(vector<T>& list) const {
        for (int i = 0; i < list.size() - 1; i++) {
            int rnd = get_random(i, list.size());
            swap(list[i], list[rnd]);
        }
    }
};
