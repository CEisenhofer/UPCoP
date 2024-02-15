#pragma once

#include "Literal.h"
#include <iostream>

struct SubtermHint;

struct Clause {

    unordered_set<optional<z3::expr>> containedVars;
    vector<Literal> literals;

    unsigned size() const { return literals.size(); }

    Clause() = default;

    Clause(const z3::expr_vector& exprs, unordered_map<string, unsigned>& nameCache);

    Clause(const Clause& c1, const Clause& c2);

    inline void AddVariables(const z3::expr_vector& exprs) {
        for (const auto& e: exprs) {
            containedVars.insert(e);
        }
    }

    inline bool operator==(const Clause& c) const {
        if (this == &c)
            return true;
        return literals == c.literals;
    }

    inline bool operator!=(const Clause& c) const {
        return !(*this == c);
    }
};

namespace std {
    template<>
    struct hash<Clause> {
        size_t operator()(const Clause& c) const {
            std::hash<Literal> hash;
            size_t idx = 17;
            for (const auto& x: c.literals) {
                idx ^= ~hash(x);
                idx *= 13;
            }
            return idx;
        }
    };
}

struct TautologyHint {
    unsigned literal1;
    unsigned literal2;
    SubtermHint* hint;

    TautologyHint() = default;

    TautologyHint(unsigned literal1, unsigned literal2, SubtermHint* hint) : literal1(literal1), literal2(literal2),
                                                                                 hint(hint) {}
};

struct IndexedClause {
    const pvector<IndexedLiteral> literals;
    const unsigned Index;
    const z3::sort_vector VarSorts;
    bool Ground;

    unsigned VarCnt() const { return VarSorts.size(); }

    unsigned size() const { return literals.size(); }

    optional<vector<TautologyHint>> TautologyConstraints;

    const IndexedLiteral* operator[](unsigned i) const {
        return literals[i];
    }

    IndexedClause() = delete;

    IndexedClause(const IndexedClause&) = delete;

    IndexedClause& operator=(const IndexedClause&) = delete;

    IndexedClause(unsigned index, const pvector<IndexedLiteral>& literals, z3::sort_vector& varSorts);

    bool operator==(const IndexedClause& c) const {
        assert((Index == c.Index) == (this == &c));
        assert(Index != c.Index || Ground == c.Ground);
        return Index == c.Index;
    }

    bool operator!=(const IndexedClause& c) const {
        return !(*this == c);
    }

    string ToString(int resolvedLiteralIdx) const;

    inline string ToString() const {
        return ToString(0);
    }
};

namespace std {
    template<>
    struct hash<IndexedClause> {
        inline size_t operator()(const IndexedClause& c) const {
            return c.Index;
        }
    };
}
