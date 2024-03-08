#pragma once
#include "term.h"

struct term;
struct term_instance;

struct fo_literal {
    string name;
    unsigned nameID;
    bool polarity;
    vector<term*> arg_bases;
    optional<z3::expr_vector> InitExprs = nullopt;

    inline unsigned arity() const { return arg_bases.size(); }

    fo_literal(string name, unsigned nameID, bool polarity, vector<term*> args) : name(std::move(name)), nameID(nameID), polarity(polarity), arg_bases(std::move(args)) { }

    fo_literal() : name("StdConstructor"), nameID(UINT32_MAX), polarity(true), arg_bases() { }

    fo_literal(z3::expr e, unordered_map<string, unsigned>& nameCache);

    inline bool can_resolve(const fo_literal& l) const {
        assert((name == l.name) == (nameID == l.nameID));
        return polarity != l.polarity && nameID == l.nameID;
    }

    inline bool operator==(const fo_literal& l) const {
        assert((name == l.name) == (nameID == l.nameID));
        return nameID == l.nameID &&
               polarity == l.polarity &&
               arg_bases == l.arg_bases;
    }

    inline bool operator!=(const fo_literal& l) const {
        return !(*this == l);
    }

    string to_string() const;
};

namespace std {
    template<>
    struct hash<fo_literal> {
        size_t operator()(const fo_literal& l) const {
            size_t ret = (l.nameID * 97127) ^ (l.polarity ? 1 : 0);
            ret += 17;
            for (const auto& arg : l.arg_bases) {
                ret = (ret * 21) ^ arg->id();
            }
            return ret;
        }
    };
}

struct indexed_literal : public fo_literal {

    const unsigned Index;

    indexed_literal() = delete;
    indexed_literal(const indexed_literal&) = delete;
    indexed_literal& operator=(const indexed_literal&) = delete;

    indexed_literal(const fo_literal& lit, unsigned index) : fo_literal(lit.name, lit.nameID, lit.polarity, lit.arg_bases), Index(index) { }

    inline bool operator==(const indexed_literal& l) const {
        assert((Index == l.Index) == (this == &l));
        return Index == l.Index;
    }

    inline bool operator!=(const indexed_literal& l) const {
        return !(*this == l);
    }
};

namespace std {
    template<>
    struct hash<indexed_literal> {
        inline size_t operator()(const indexed_literal& l) const {
            return l.Index;
        }
    };
}
