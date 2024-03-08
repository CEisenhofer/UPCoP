#pragma once

#include "adt_solver.h"
#include "CLIParser.h"
#include "cnf.h"
#include "ground_literal.h"
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
    vector<pair<term*, term*>> equalities;

public:

    subterm_hint() = default;

    subterm_hint(vector<pair<term*, term*>> equalities, bool swapped) : swapped(swapped), equalities(std::move(equalities)) { }

    void GetPosConstraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2, vector<formula>& constraints) const;
    formula GetNegConstraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const;

    bool IsSatisfied(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const;

    inline pair<int, int> GetCpyIdx(const ground_literal& l1, const ground_literal& l2) const {
        // return (l1.CopyIndex, l2.CopyIndex);
        return !swapped ? make_pair(l1.copyIdx, l2.copyIdx) : make_pair(l2.copyIdx, l1.copyIdx);
    }

    bool tautology() const {
        return equalities.empty();
    }

    subterm_hint* swap() const {
        return new subterm_hint(equalities, !swapped);
    }

    void add(term* t1, term* t2) {
        equalities.emplace_back(t1, t2);
    }
};

// TODO: Merge with matrix propagator
struct propagator_base : public CaDiCal_propagator {

    mutable std::default_random_engine generator;
    mutable std::uniform_int_distribution<unsigned> distribution;

protected:

    ProgParams& progParams;
    const cnf<indexed_clause*>& matrix;

public:
    complex_adt_solver& term_solver;
    bool Running = true;

    propagator_base(propagator_base&) = delete;
    propagator_base& operator=(propagator_base&) = delete;

    // [min, max)
    unsigned getRandom(unsigned min, unsigned max) const;

    propagator_base(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt);

    large_array unificationHints;

protected:

    // Return: null - infeasible to unify
    // Returns 0 length - always unifies
    // Returns n length - given n elements have (and could) unify
    static subterm_hint* CollectConstrainUnifiable(const ground_literal& l1, const indexed_literal& l2) ;

public:

    void cache_unification(const ground_literal& l1, const indexed_literal& l2);

    inline void cache_unification(const ground_literal& l1, const ground_literal& l2) {
        return cache_unification(l1, *l2.lit);
    }

public:

    static string clause_to_string(const vector<ground_literal>& ground, unordered_map<term_instance*, string>* prettyNames);

    static string pretty_print_literal(const fo_literal* l, unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames);

    static string pretty_print_literal(const ground_literal& l, unordered_map<term_instance*, string>* prettyNames) {
        return pretty_print_literal(l.lit, l.copyIdx, prettyNames);
    }

protected:

    template<typename T>
    void Shuffle(vector<T>& list) const {
        for (int i = 0; i < list.size() - 1; i++) {
            int rnd = getRandom(i, list.size());
            swap(list[i], list[rnd]);
        }
    }
};

