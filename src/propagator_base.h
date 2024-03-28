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

class large_array final {
    // This is fine, as the class is longer than one; the index is invalid for sure
#define FAILED_PTR ((subterm_hint*)-1)
    unsigned size;
    optional<vector<const subterm_hint*>> small;
    optional<unordered_map<pair<unsigned, unsigned>, const subterm_hint*>> large;

public:

    large_array(unsigned size);
    ~large_array();

    const subterm_hint* get(unsigned i, unsigned j) const;
    void set(unsigned i, unsigned j, const subterm_hint* hint);
    void set_invalid(unsigned i, unsigned j) {
        return set(i, j, FAILED_PTR);
    }
    static bool is_invalid(const subterm_hint* hint) {
        assert(hint != nullptr);
        return hint == FAILED_PTR;
    }
};

class subterm_hint final {

    const bool swapped = false;
    vector<pair<const term*, const term*>> equalities;

public:

    subterm_hint() = default;

    subterm_hint(vector<pair<const term*, const term*>> equalities, bool swapped) : swapped(swapped), equalities(std::move(equalities)) { }

    void get_pos_constraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2, vector<formula>& constraints) const;
    formula get_neg_constraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const;

    bool is_satisfied(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const;

    inline pair<int, int> get_cpy_idx(const ground_literal& l1, const ground_literal& l2) const {
        // return (l1.CopyIndex, l2.CopyIndex);
        return !swapped ? make_pair(l1.copyIdx, l2.copyIdx) : make_pair(l2.copyIdx, l1.copyIdx);
    }

    bool tautology() const {
        return equalities.empty();
    }

    subterm_hint* swap() const {
        return new subterm_hint(equalities, !swapped);
    }

    void add(const term* t1, const term* t2) {
        equalities.emplace_back(t1, t2);
    }
};

// TODO: Merge with matrix propagator
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

    large_array unificationHints;

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

    propagator_base(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft);
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

    // Return: null - infeasible to unify
    // Returns 0 length - always unifies
    // Returns n length - given n elements have (and could) unify
    static subterm_hint* collect_constrain_unifiable(const ground_literal& l1, const indexed_literal& l2) ;

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

    const subterm_hint* cache_unification(const ground_literal& l1, const indexed_literal& l2);

    inline const subterm_hint* cache_unification(const ground_literal& l1, const ground_literal& l2) {
        return cache_unification(l1, *l2.lit);
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

    template<typename T>
    void Shuffle(vector<T>& list) const {
        for (int i = 0; i < list.size() - 1; i++) {
            int rnd = get_random(i, list.size());
            swap(list[i], list[rnd]);
        }
    }
};
