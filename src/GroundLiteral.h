#pragma once
#include "Literal.h"

struct PropagatorBase;

struct GroundLiteral {
    IndexedLiteral* Literal;
    unsigned CopyIndex;
    unsigned GetArity() const { return Literal->Arity(); }

    GroundLiteral() : Literal(nullptr), CopyIndex(0) { }

    GroundLiteral(IndexedLiteral* lit, int copyIndex) :
        Literal(lit), CopyIndex(copyIndex) { }

    inline bool operator==(const GroundLiteral& l) const {
        return *Literal == *l.Literal && CopyIndex == l.CopyIndex;
    }

    inline bool operator!=(const GroundLiteral& l) const {
        return !(*this == l);
    }

    string ToString() const;
};

namespace std {
    template<>
    struct hash<GroundLiteral> {
        size_t operator()(const GroundLiteral& l) const {
            static std::hash<IndexedLiteral> hash;
            return ((hash(*l.Literal) ^ 40883) * 13) ^ (l.CopyIndex * 14753);
        }
    };
}
