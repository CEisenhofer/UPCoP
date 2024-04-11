#pragma once

#include "utils.h"

#include <chrono>

class propagator_base;

class z3_propagator : public z3::user_propagator_base {
    friend class formula_manager;

    z3::context* ctx;
    z3::solver* s;
    propagator_base* const base;

    int var_cnt = 0;
    std::vector<unsigned> undo_stack_limit;
    std::vector<tri_state> interpretation;

    z3::expr_vector assumptions;
    bool coreQueried = false;
    unordered_set<z3::expr> core;

    const z3::sort_vector empty_sort_vector;

    unordered_map<z3::expr, unsigned> z3ToIdx;
    z3::expr_vector idxToZ3;

#if !defined(NDEBUG) && false
    z3::on_clause_eh_t onClauseEh;
    z3::on_clause onClause;
#endif

public:

    formula_manager m;

    inline z3::context& get_ctx() {
        return *ctx;
    }

    inline z3::solver& get_solver() {
        return *s;
    }

    inline propagator_base* get_base() {
        return base;
    }

    inline z3::expr get_expr(int lit) const {
        assert(lit != 0);
        z3::expr e = idxToZ3[abs(lit)];
        if (lit < 0)
            return !e;
        return e;
    }

    inline z3::expr get_expr(literal lit) const {
        return get_expr(lit->get_lit());
    }

    tri_state check() {
        core.clear();
        coreQueried = false;
        auto res = s->check(assumptions);
        assumptions.resize(0);
        switch (res) {
            case z3::sat:
                return sat;
            case z3::unsat:
                return unsat;
            default:
                return undef;
        }
    }

#ifndef NDEBUG
    void output_literals(const justification& just) const;
    void output_literals(const z3::expr_vector& lit, const z3::expr_vector& lhs, const z3::expr_vector& rhs);
#endif

    void propagate_conflict(const justification& just);
    bool propagate(const justification& just, literal prop);

    z3_propagator(z3::context* ctx, z3::solver* s, propagator_base* base, unsigned timeLeft);

    bool get_value(literal v, bool& value) const {
        tri_state val = interpretation[abs(v->get_lit()) - 1];
        if (val == undef)
            return false;
        value = val == sat;
        return true;
    }

    inline bool has_value(literal v) const {
        return interpretation[abs(v->get_lit()) - 1] != undef;
    }

    inline void assume(literal v) {
        assumptions.push_back(get_expr(v));
    }

    inline void add_assertion(z3::expr e) {
        s->add(e);
    }

    inline void add_assertion(literal v) {
        s->add(get_expr(v));
    }

    inline void add_assertion(vector<literal> v) {
        // TODO: Do this over the formula manager
        z3::expr_vector vec(*ctx);
        for (auto&& lit : v) {
            vec.push_back(get_expr(lit));
        }
        s->add(z3::mk_or(vec));
    }

    bool failed(literal v) {
        if (!coreQueried) {
            coreQueried = true;
            auto coreList = s->unsat_core();
            for (auto&& e : coreList) {
                core.insert(e);
            }
        }
        return contains(core, get_expr(v));
    }

    int new_var_raw() {
        int newId = ++var_cnt;
        interpretation.push_back(undef);
        assert(var_cnt == interpretation.size());
        return newId;
    }

    static z3_propagator* create(propagator_base* base, unsigned timeLeft) {
        auto* ctx = new z3::context();
        auto* s = new z3::solver(*ctx, z3::solver::simple());
        // s->set("smt.relevancy", (unsigned)0);
        return new z3_propagator(ctx, s, base, timeLeft);
    }

#ifndef NDEBUG

    inline int new_observed_var(const std::string& name) {
        signed newId = new_var_raw();
        z3::expr e = fresh_user_constant(*ctx, name, ctx->bool_sort());
        names.insert(std::make_pair(newId, name));
        z3ToIdx.insert(std::make_pair(e, newId));
        idxToZ3.push_back(e);
        return newId;
    }

    inline int register_observed_var(const z3::expr& e, const std::string& name) {
        signed newId = new_var_raw();
        names.insert(std::make_pair(newId, name));
        z3ToIdx.insert(std::make_pair(e, newId));
        idxToZ3.push_back(e);
        return newId;
    }

#else

    inline int new_observed_var() {
        signed newId = new_var_raw();
        z3::expr e = fresh_user_constant(*ctx, "v", ctx->bool_sort());
        z3ToIdx.insert(std::make_pair(e, newId));
        idxToZ3.push_back(e);
        return newId;
    }

#define register_observed_var(X, Y) register_observed_var2(X)

    inline int register_observed_var2(const z3::expr& e) {
        signed newId = new_var_raw();
        z3ToIdx.insert(std::make_pair(e, newId));
        idxToZ3.push_back(e);
        return newId;
    }

#endif

protected:

    void fixed(const z3::expr& e, const z3::expr& v) final;

    void eq(const z3::expr& lhs, const z3::expr& rhs) final;

    void diseq(const z3::expr& lhs, const z3::expr& rhs) final;

    void push() final;

    void pop(unsigned lvl) final;

    void final() final;

    void created(const z3::expr& e) final {
    }

    z3::user_propagator_base* fresh(z3::context& ctx) final {
        return this;
    }
};
