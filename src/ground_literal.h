#pragma once
#include "fo_literal.h"

struct propagator_base;

struct ground_literal {
    indexed_literal* lit;
    unsigned copyIdx;
    unsigned arity() const { return lit->arity(); }

    ground_literal() : lit(nullptr), copyIdx(0) { }

    ground_literal(indexed_literal* lit, int copyIndex) :
            lit(lit), copyIdx(copyIndex) { }

    inline bool operator==(const ground_literal& l) const {
        return *lit == *l.lit && copyIdx == l.copyIdx;
    }

    inline bool operator!=(const ground_literal& l) const {
        return !(*this == l);
    }

#ifndef NDEBUG
    string to_string() const;
#endif
};

namespace std {
    template<>
    struct hash<ground_literal> {
        size_t operator()(const ground_literal& l) const {
            static std::hash<indexed_literal> hash;
            return ((hash(*l.lit) ^ 40883) * 13) ^ ((size_t)l.copyIdx * 14753);
        }
    };
}
