#pragma once

#include "cadical.hpp"
#include "formula.h"

#include <chrono>

class propagator_base;

class CaDiCal_propagator : public CaDiCaL::ExternalPropagator, public CaDiCaL::Terminator, public CaDiCaL::FixedAssignmentListener {
    friend class formula_manager;

    propagator_base* const base;

#ifdef DIMACS
    std::stringstream dimacs;
#endif

private:

    decltype(std::chrono::high_resolution_clock::now()) stopTime;

    int var_cnt = 0;
    std::vector<unsigned> undo_stack_limit;

    unsigned pending_hard_propagations_idx = 0;
    unsigned hard_propagation_read_idx = 0;
    std::vector<std::vector<int>> pending_hard_propagations;

    std::vector<unsigned> soft_propagation_limit;
    std::vector<std::pair<std::vector<int>, int>> pending_soft_propagations;
    unsigned soft_propagations_explanation_idx = 0;
    std::vector<std::vector<int>> soft_justifications;
    unsigned soft_propagation_read_idx = 0;

    std::vector<tri_state> interpretation;

    // for persistent propagation
    std::unordered_set<std::vector<int>> prev_propagations;

    unsigned literal_to_idx(int lit) const {
        return 2 * abs(lit) + (unsigned)(lit < 0) - 2 /* 0 is not a valid literal*/;
    }

protected:
    std::vector<bool> interpreted;

public:

    CaDiCaL::Solver* solver = nullptr;
    formula_manager m;

    inline unsigned decision_level() const {
        return  undo_stack_limit.size();
    }

    tri_state check() {
        switch (solver->solve()) {
            case 10:
                return sat;
            case 20:
                return unsat;
            default:
                return undef;
        }
    }

    unsigned vars() {
        return (unsigned)solver->vars();
    }

#ifdef DIMACS
    string get_dimacs() {
        string clauses = dimacs.str();
        unsigned cnt = 0;
        for (char c : clauses) {
            cnt += (unsigned)(c == '\n');
        }
        string ret = "p cnf " + std::to_string(vars()) + " " + to_string(cnt - 1) + "\n";
        ret += dimacs.str();
        return ret;
    }
#endif

#ifndef NDEBUG
    void output_literals(const std::vector<literal>& lit) const;
#endif

    void propagate_conflict(const justification& just);

    bool hard_propagate(const justification& just, formula prop);

    bool soft_propagate(const justification& just, literal prop);

    CaDiCal_propagator(propagator_base* base, unsigned timeLeft);
    ~CaDiCal_propagator();

    inline bool get_value(literal v, bool& value) const {
        tri_state val = interpretation[abs(v->get_lit()) - 1];
        if (val == undef)
            return false;
        value = val == sat;
        return true;
    }

    inline bool has_value(literal v) const {
        return interpretation[abs(v->get_lit()) - 1] != undef;
    }

    inline bool is_skip(literal v) const {
        return !interpreted[abs(v->get_lit()) - 1];
    }

    inline void assume(literal v) const {
        solver->assume(v->get_lit());
    }

    inline void add_assertion(literal v) const {
        solver->clause(v->get_lit());
    }

    inline void add_assertion(const vector<literal>& v) const {
        for (literal l : v) {
            solver->add(l->get_lit());
        }
        solver->add(0);
    }

    inline bool failed(literal v) const {
        return solver->failed(v->get_lit());
    }

    int new_var_raw(bool is_interesting) {
        int newId = ++var_cnt;
        soft_justifications.emplace_back();
        soft_justifications.emplace_back();
        assert(2 * var_cnt == soft_justifications.size());
        interpretation.push_back(undef);
        interpreted.push_back(is_interesting);
        assert(var_cnt == interpretation.size());
        return newId;
    }

#ifndef NDEBUG

    inline int new_observed_var(const std::string& name) {
        signed newId = new_var_raw(true);
        solver->add_observed_var(newId);
        names.insert(std::make_pair(newId, name));
        return newId;
    }

    inline int new_var(const std::string& name) {
        signed newId = new_var_raw(false);
        solver->add_observed_var(newId);
        names.insert(std::make_pair(newId, name));
        return newId;
    }

#else

    int new_observed_var() {
        signed newId = new_var_raw(true);
        solver->add_observed_var(newId);
        return newId;
    }

    int new_var() {
        signed newId = new_var_raw(false);
        solver->add_observed_var(newId);
        return newId;
    }
#endif

    inline void observe_again(int var_id) {
        solver->add_observed_var(var_id);
    }

    inline void observe_remove(int var_id) {
        // solver->remove_observed_var(var_id);
        // solver->melt(var_id);
    }

protected:

    void notify_assignment(const vector<int>& lits) final;

    void notify_fixed_assignment(int id) final;

    bool terminate() override {
        return std::chrono::high_resolution_clock::now() >= stopTime;
    }

    void notify_new_decision_level() final;

    void notify_backtrack(size_t new_level) final;

    bool cb_check_found_model(const std::vector<int>& model) final;

    int cb_propagate() final;

    int cb_add_reason_clause_lit(int propagated_lit) final;

    bool cb_has_external_clause(bool& is_forgettable) final;

    int cb_add_external_clause_lit() final;

    int cb_decide() final;
};
