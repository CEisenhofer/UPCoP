#pragma once

// #define PUSH_POP

#include <optional>
#include <algorithm>
#include <sstream>
#include <unordered_set>
#include "z3++.h"

#ifndef NDEBUG
#define DEBUG
#endif

#ifndef NDEBUG
// typedef term* expr;
#else
// typedef cnf expr;
#endif

using namespace std;

inline string to_lower(const string& s) {
    string ret = s;
    transform(ret.begin(), ret.end(), ret.begin(),
                   [](unsigned char ch) { return tolower(ch); });
    return ret;
}

inline bool to_uint(char* c, unsigned& ret) {
    stringstream ss;
    ss << c;
    ret = (unsigned) -1;
    ss >> ret;
    if (ss.fail())
        return false;
    return true;
}

inline bool to_int(char* c, int& ret) {
    stringstream ss;
    ss << c;
    ret = UINT32_MAX;
    ss >> ret;
    if (ss.fail())
        return false;
    return true;
}

void start_watch();
uint64_t stop_watch();

template<typename T, typename S, typename hash, typename eq>
inline vector<pair<T, S>> to_sorted_vector(const unordered_map<T, S, hash, eq>& map) {
    return to_sorted_vector(map, [](const std::pair<T, S>& a, const pair<T, S>& b) {
        return a.first < b.first;
    });
}

template<typename T, typename S, class P, typename hash, typename eq>
inline vector<pair<T, S>> to_sorted_vector(const unordered_map<T, S, hash, eq>& map, const P& pred) {
    vector<pair<T, S>> ret;
    ret.reserve(map.size());
    for (auto& entry : map) {
        ret.emplace_back(entry);
    }
    sort(ret.begin(), ret.end(), pred);
    return ret;
}

template<typename T, typename S, typename hash, typename eq>
inline bool tryGetValue(unordered_map<T, S, hash, eq>& map, const T& key, S*& value) {
    const auto& it = map.find(key);
    if (it == map.cend())
        return false;
    value = &it->second;
    return true;
}

template<typename T, typename S, typename hash, typename eq>
inline bool tryGetValue(const unordered_map<T, S, hash, eq>& map, const T& key, S& value) {
    const auto& it = map.find(key);
    if (it == map.cend())
        return false;
    value = it->second;
    return true;
}

template<typename T, typename hash, typename eq>
inline bool contains(const unordered_set<T, hash, eq>& set, const T& key) {
    const auto& it = set.find(key);
    return it != set.end();
}

template<typename T, typename S, typename hash, typename eq>
inline bool contains_key(const unordered_map<T, S, hash, eq>& set, const T& key) {
    const auto& it = set.find(key);
    return it != set.end();
}

namespace std {
    template<>
    struct hash<z3::expr> {
        inline size_t operator()(const z3::expr& x) const {
            return (size_t) x.hash();
        }
    };

    template<>
    struct equal_to<z3::expr> {
        inline bool operator()(const z3::expr& x, const z3::expr& y) const {
            return z3::eq(x, y);
        }
    };

    template<>
    struct hash<z3::func_decl> {
        inline size_t operator()(const z3::func_decl& x) const {
            return (size_t) x.hash();
        }
    };

    template<>
    struct hash<optional<z3::func_decl>> {
        inline size_t operator()(const optional<z3::func_decl>& x) const {
            if (!x.has_value())
                return 0;
            return x->hash();
        }
    };

    template<>
    struct equal_to<z3::func_decl> {
        inline bool operator()(const z3::func_decl& x, const z3::func_decl& y) const {
            return z3::eq(x, y);
        }
    };

    template<>
    struct equal_to<optional<z3::func_decl>> {
        inline bool operator()(const optional<z3::func_decl>& x, const optional<z3::func_decl>& y) const {
            if (x.has_value() != y.has_value())
                return false;
            if (!x.has_value())
                return true;
            return z3::eq(*x, *y);
        }
    };

    template<>
    struct hash<z3::sort> {
        inline size_t operator()(const z3::sort& x) const {
            return (size_t) x.hash();
        }
    };

    template<>
    struct equal_to<z3::sort> {
        inline bool operator()(const z3::sort& x, const z3::sort& y) const {
            return z3::eq(x, y);
        }
    };

    template<>
    struct hash<std::vector<int>> {
        inline size_t operator()(const std::vector<int>& x) const {
            size_t ret = 0;
            for (int v : x) {
                ret = (324723947 * ret + v) ^ 93485734985;
            }
            return ret;
        }
    };

    template<>
    struct equal_to<std::vector<int>> {
        inline bool operator()(const std::vector<int>& x, const std::vector<int>& y) const {
            return x == y;
        }
    };
}

inline void add_range(z3::expr_vector& v, const z3::expr_vector& other) {
    const unsigned i = v.size();
    v.resize(i + other.size());
    for (unsigned j = 0; j < other.size(); j++) {
        z3::ast ast = other[j];
        v.set(i + j, ast);
    }
}

template<typename T>
inline void add_range(vector<T>& v, const vector<T>& other) {
    v.insert(v.end(), other.begin(), other.end());
}

inline z3::expr FreshUserConstant(z3::context& ctx, const string& prefix, const z3::sort& sort) {
    Z3_func_decl decl = Z3_mk_fresh_func_decl(ctx, prefix.c_str(), 0, nullptr, sort);
    z3::func_decl fresh = z3::func_decl(ctx, decl);
    z3::expr e = ctx.user_propagate_function(fresh.name(), z3::sort_vector(ctx), sort)();
    return e;
}

inline z3::expr FreshConstant(z3::context& ctx, const string& prefix, const z3::sort& sort) {
    Z3_ast e = Z3_mk_fresh_const(ctx, prefix.c_str(), sort);
    return { ctx, e };
}

inline z3::func_decl FreshFunction(z3::context& ctx, const string& prefix, const z3::sort_vector& domain, const z3::sort& sort) {
    z3::array<Z3_sort> args(domain.size());
    for (unsigned i = 0; i < args.size(); i++) {
        args[(int)i] = domain[i];
    }
    Z3_func_decl decl = Z3_mk_fresh_func_decl(ctx, prefix.c_str(), args.size(), args.ptr(), sort);
    return { ctx, decl };
}

inline z3::expr_vector Reverse(const z3::expr_vector& v) {
    z3::expr_vector ret(v.ctx());
    ret.resize(v.size());
    for (unsigned i = 0; i < v.size(); i++) {
        z3::expr e = v[v.size() - (i + 1)];
        ret.set(i, e);
    }
    return ret;
}

struct solving_exception : public exception {
    string msg;

    explicit solving_exception(const string& msg) : msg(msg) {}

    const char* what() const noexcept override {
        return msg.c_str();
    }
};

template<typename T>
inline std::string string_join(const std::vector<T*>& args, const std::string& sep) {
    assert(!args.empty());
    if (args.size() == 1)
        return args[0]->to_string();
    std::stringstream sb;
    sb << "(" << args[0]->to_string();
    for (unsigned i = 1; i < args.size(); i++) {
        sb << sep << args[i]->to_string();
    }
    sb << ")";
    return sb.str();
}


template<typename T>
inline std::string string_join(const std::vector<T>& args, const std::string& sep) {
    assert(!args.empty());
    if (args.size() == 1)
        return args[0].to_string();
    std::stringstream sb;
    sb << "(" << args[0].to_string();
    for (unsigned i = 1; i < args.size(); i++) {
        sb << sep << args[i].to_string();
    }
    sb << ")";
    return sb.str();
}