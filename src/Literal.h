#pragma once
#include "Term.h"

struct Term;
struct term_instance;

struct Literal {
    string name;
    unsigned nameID;
    bool polarity;
    pvector<Term> ArgBases;
    optional<z3::expr_vector> InitExprs = nullopt;

    inline unsigned Arity() const { return ArgBases.size(); }

    Literal(string name, unsigned nameID, bool polarity, pvector<Term> args) : name(std::move(name)), nameID(nameID), polarity(polarity), ArgBases(std::move(args)) { }

    Literal() : name("StdConstructor"), nameID(UINT32_MAX), polarity(true), ArgBases() { }

    Literal(z3::expr e, unordered_map<string, unsigned>& nameCache);

    inline bool CanResolve(const Literal& l) const {
        assert((name == l.name) == (nameID == l.nameID));
        return polarity != l.polarity && nameID == l.nameID;
    }

    z3::expr_vector GetInstances(const z3::expr_vector& args);

    inline bool operator==(const Literal& l) const {
        assert((name == l.name) == (nameID == l.nameID));
        return nameID == l.nameID &&
               polarity == l.polarity &&
               ArgBases == l.ArgBases;
    }

    inline bool operator!=(const Literal& l) const {
        return !(*this == l);
    }

    string ToString() const;
};

namespace std {
    template<>
    struct hash<Literal> {
        size_t operator()(const Literal& l) const {
            size_t ret = (l.nameID * 97127) ^ (l.polarity ? 1 : 0);
            ret += 17;
            for (const auto& arg : l.ArgBases) {
                ret = (ret * 21) ^ arg->HashID;
            }
            return ret;
        }
    };
}

struct IndexedLiteral : public Literal {

    const unsigned Index;

    IndexedLiteral() = delete;
    IndexedLiteral(const IndexedLiteral&) = delete;
    IndexedLiteral& operator=(const IndexedLiteral&) = delete;

    IndexedLiteral(const Literal& lit, unsigned index) : Literal(lit.name, lit.nameID, lit.polarity, lit.ArgBases), Index(index) { }

    inline bool operator==(const IndexedLiteral& l) const {
        assert((Index == l.Index) == (this == &l));
        return Index == l.Index;
    }

    inline bool operator!=(const IndexedLiteral& l) const {
        return !(*this == l);
    }
};

namespace std {
    template<>
    struct hash<IndexedLiteral> {
        inline size_t operator()(const IndexedLiteral& l) const {
            return l.Index;
        }
    };
}
