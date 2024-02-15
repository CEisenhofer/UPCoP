#pragma once

#include "ADTSolver.h"
#include "CadicalWrapper.h"
#include "CLIParser.h"
#include "CNF.h"
#include "GroundLiteral.h"
#include <random>

class SubtermHint;

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

class Large2DArray final {
    // This is fine, as the class is longer than one; the index is invalid for sure
#define FAILED_PTR ((SubtermHint*)-1)
    unsigned size;
    optional<pvector<const SubtermHint>> small;
    optional<unordered_map<pair<unsigned, unsigned>, const SubtermHint*>> large;

public:

    Large2DArray(unsigned size);
    ~Large2DArray();

    const SubtermHint* get(unsigned i, unsigned j) const;
    void set(unsigned i, unsigned j, const SubtermHint* hint);
    void set_invalid(unsigned i, unsigned j) {
        return set(i, j, FAILED_PTR);
    }
    static bool is_invalid(const SubtermHint* hint) {
        assert(hint != nullptr);
        return hint == FAILED_PTR;
    }
};

class SubtermHint final {

    const bool swapped = false;
    vector<pair<Term*, Term*>> equalities;

public:

    SubtermHint() = default;

    SubtermHint(vector<pair<Term*, Term*>> equalities, bool swapped) : swapped(swapped), equalities(std::move(equalities)) { }

    void GetPosConstraints(PropagatorBase& propagator, const GroundLiteral& l1, const GroundLiteral& l2, vector<formula>& constraints) const;
    formula GetNegConstraints(PropagatorBase& propagator, const GroundLiteral& l1, const GroundLiteral& l2) const;

    bool IsSatisfied(const GroundLiteral& l1, const GroundLiteral& l2) const;

    inline pair<int, int> GetCpyIdx(const GroundLiteral& l1, const GroundLiteral& l2) const {
        // return (l1.CopyIndex, l2.CopyIndex);
        return !swapped ? make_pair(l1.CopyIndex, l2.CopyIndex) : make_pair(l2.CopyIndex, l1.CopyIndex);
    }

    bool tautology() const {
        return equalities.empty();
    }

    SubtermHint* swap() const {
        return new SubtermHint(equalities, !swapped);
    }

    void add(Term* t1, Term* t2) {
        equalities.emplace_back(t1, t2);
    }
};

struct PropagatorBase : public CaDiCalPropagator {

    mutable std::default_random_engine generator;
    mutable std::uniform_int_distribution<unsigned> distribution;

protected:

    const ProgParams& progParams;
    const CNF<IndexedClause*>& matrix;

    pvector<IndexedClause> initClauses;
    bool is_conflict = false;

public:
    ComplexADTSolver& term_solver;
    bool Running = true;

    PropagatorBase(PropagatorBase&) = delete;
    PropagatorBase& operator=(PropagatorBase&) = delete;

    // [min, max)
    unsigned getRandom(unsigned min, unsigned max) const;

    PropagatorBase(CNF<IndexedClause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt);

public:

    Large2DArray UnificationHints;
    bool Satisfiable = false;

    inline void add_undo(const action& action) {
        undoStack.push_back(action);
    }

protected:

    // Return: null - infeasible to unify
    // Returns 0 length - always unifies
    // Returns n length - given n elements have (and could) unify
    SubtermHint* CollectConstrainUnifiable(const GroundLiteral& l1, const IndexedLiteral& l2) const;

public:

    void CacheUnification(const GroundLiteral& l1, const IndexedLiteral& l2);

    inline void CacheUnification(const GroundLiteral& l1, const GroundLiteral& l2) {
        return CacheUnification(l1, *l2.Literal);
    }

private:

    void CreateTautologyConstraints(IndexedClause& clause);

    void fixed(literal var, bool value) override;

    virtual void fixed2(literal lit, bool value) = 0;

public:

    static string ClauseToString(const vector<GroundLiteral>& ground, unordered_map<variableIdentifier, string>* prettyNames);

    static string PrettyPrintLiteral(const Literal* l, unsigned cpyIdx, unordered_map<variableIdentifier, string>* prettyNames);

    static string PrettyPrintLiteral(const GroundLiteral& l, unordered_map<variableIdentifier, string>* prettyNames) {
        return PrettyPrintLiteral(l.Literal, l.CopyIndex, prettyNames);
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

