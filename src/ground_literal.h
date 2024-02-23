#pragma once
#include "fo_literal.h"

struct propagator_base;

struct ground_literal {
    indexed_literal* Literal;
    unsigned CopyIndex;
    unsigned GetArity() const { return Literal->Arity(); }

    ground_literal() : Literal(nullptr), CopyIndex(0) { }

    ground_literal(indexed_literal* lit, int copyIndex) :
        Literal(lit), CopyIndex(copyIndex) { }

    inline bool operator==(const ground_literal& l) const {
        return *Literal == *l.Literal && CopyIndex == l.CopyIndex;
    }

    inline bool operator!=(const ground_literal& l) const {
        return !(*this == l);
    }

    string ToString() const;
};

namespace std {
    template<>
    struct hash<ground_literal> {
        size_t operator()(const ground_literal& l) const {
            static std::hash<indexed_literal> hash;
            return ((hash(*l.Literal) ^ 40883) * 13) ^ (l.CopyIndex * 14753);
        }
    };
}
