#pragma once

#include "fo_literal.h"
#include <iostream>

struct subterm_hint;

struct clause {

    unordered_set<optional<z3::expr>> containedVars;
    vector<fo_literal> literals;
    bool Conjecture = false;

    unsigned size() const { return literals.size(); }

    clause() = default;

    clause(const z3::expr_vector& exprs, unordered_map<string, unsigned>& nameCache);

    clause(const clause& c1, const clause& c2);

    inline void AddVariables(const z3::expr_vector& exprs) {
        for (const auto& e : exprs) {
            containedVars.insert(e);
        }
    }

    inline bool operator==(const clause& c) const {
        if (this == &c)
            return true;
        return literals == c.literals;
    }

    inline bool operator!=(const clause& c) const {
        return !(*this == c);
    }
};

namespace std {
    template<>
    struct hash<clause> {
        size_t operator()(const clause& c) const {
            std::hash<fo_literal> hash;
            size_t idx = 17;
            for (const auto& x : c.literals) {
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
    subterm_hint* hint;

    TautologyHint() = default;

    TautologyHint(unsigned literal1, unsigned literal2, subterm_hint* hint) : literal1(literal1), literal2(literal2),
                                                                              hint(hint) {}
};

struct indexed_clause {
    const vector<indexed_literal*> literals;
    const vector<term*> variables;
    const unsigned index;
    const bool ground;
    bool conjecture = false;

    unsigned size() const { return literals.size(); }

    optional<vector<TautologyHint>> TautologyConstraints;

    const indexed_literal* operator[](unsigned i) const {
        return literals[i];
    }

    indexed_clause() = delete;

    indexed_clause(const indexed_clause&) = delete;

    indexed_clause& operator=(const indexed_clause&) = delete;

    indexed_clause(unsigned index, vector<indexed_literal*> literals, vector<term*> variables);

    bool operator==(const indexed_clause& c) const {
        assert((index == c.index) == (this == &c));
        assert(index != c.index || ground == c.ground);
        return index == c.index;
    }

    bool operator!=(const indexed_clause& c) const {
        return !(*this == c);
    }

    string to_string(int resolvedLiteralIdx) const;

    inline string to_string() const {
        return to_string(0);
    }
};

namespace std {
    template<>
    struct hash<indexed_clause> {
        inline size_t operator()(const indexed_clause& c) const {
            return c.index;
        }
    };
}
