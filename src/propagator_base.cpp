#include "matrix_propagator.h"
#include "CadicalWrapper.h"
#include "Z3Wrapper.h"
#include <iostream>

unsigned propagator_base::get_random(unsigned min, unsigned max) const {
    assert(max > min);
    unsigned res = distribution(generator);
    unsigned span = max - min;
    return min + res % span;
}

propagator_base::propagator_base(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft)
    : z3Propagator(progParams.smt ? z3_propagator::create(this, timeLeft) : nullptr), cadicalPropagator(!progParams.smt ? new CaDiCal_propagator(this, timeLeft) : nullptr),
    term_solver(adtSolver), m(z3Propagator != nullptr ? z3Propagator->m : cadicalPropagator->m), generator(0), progParams(progParams), matrix(cnf), unificationHints(literalCnt)
     {

    term_solver.set((matrix_propagator*)this);
    if (z3Propagator != nullptr)
        adtSolver.make_z3_us(z3Propagator->get_ctx());
}

propagator_base::~propagator_base() {
    term_solver.clear();
    if (z3Propagator != nullptr) {
        z3::context* ctx;
        z3::solver* s;
        ctx = &z3Propagator->get_ctx();
        s = &z3Propagator->get_solver();
        delete z3Propagator;
        delete s;
        delete ctx;
    }
    delete cadicalPropagator;
}

large_array::large_array(unsigned size) : size(size) {
    if (size < (1 << 14)) {
        small = make_optional(vector<const subterm_hint*>());
        small->resize((size_t)size * size);
        large = nullopt;
    } else {
        small = nullopt;
        large = make_optional(unordered_map<pair<unsigned, unsigned>, const subterm_hint*>(14591 /* some large prime */));
    }
}

large_array::~large_array() {
    if (small.has_value()) {
        for (const subterm_hint* r: small.value()) {
            if (r != nullptr && !is_invalid(r))
                delete r;
        }
    } else {
        for (auto r: large.value()) {
            if (r.second != nullptr && !is_invalid(r.second))
                delete r.second;
        }
    }
}

const subterm_hint* large_array::get(unsigned i, unsigned j) const {
    if (small.has_value())
        return (*small)[i * size + j];
    const subterm_hint* res = nullptr;
    if (tryGetValue(*large, make_pair(i, j), res))
        return res;
    return nullptr;
}

void large_array::set(unsigned i, unsigned j, const subterm_hint* hint) {
    if (small.has_value()) {
        assert((*small)[i * size + j] == nullptr);
        (*small)[i * size + j] = hint;
        return;
    }
    assert(large->find(make_pair(i, j)) == large->end());
    large->insert(make_pair(make_pair(i, j), hint));
}

void subterm_hint::get_pos_constraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2, vector<formula>& constraints) const {
    auto [lhsCpy, rhsCpy] = get_cpy_idx(l1, l2);
    for (auto [lhs, rhs]: equalities) {
        formula e = propagator.term_solver.make_equality_expr(lhs->get_instance(lhsCpy, propagator), rhs->get_instance(rhsCpy, propagator));
        if (e->is_false()) {
            constraints.resize(0);
            constraints.push_back(propagator.m.mk_false());
            return;
        }
        if (e->is_true())
            continue;
        constraints.push_back(e);
    }
}

formula subterm_hint::get_neg_constraints(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const {
    auto [lhsCpy, rhsCpy] = get_cpy_idx(l1, l2);
    vector<formula_term*> orList;
    for (const auto& [lhs, rhs] : equalities) {
        formula e = propagator.term_solver.make_equality_expr(lhs->get_instance(lhsCpy, propagator), rhs->get_instance(rhsCpy, propagator));
        if (e->is_false())
            return propagator.m.mk_true();
        if (e->is_true())
            continue;
        orList.push_back(propagator.m.mk_not(e));
    }
    return propagator.m.mk_or(orList);
}

bool subterm_hint::is_satisfied(matrix_propagator& propagator, const ground_literal& l1, const ground_literal& l2) const {
    auto [lhsCpy, rhsCpy] = get_cpy_idx(l1, l2);
    for (const auto& [lhs, rhs]: equalities) {
        if (!complex_adt_solver::are_equal(lhs->get_instance(lhsCpy, propagator), rhs->get_instance(rhsCpy, propagator)))
            return false;
    }
    return true;
}

subterm_hint* propagator_base::collect_constrain_unifiable(const ground_literal& l1, const indexed_literal& l2) {
    // l1 has to be ground; otw. P(:auto 0) [l1] and P(:auto 0) [l2] would say that they are always equal
    auto* hint = new subterm_hint();
    unsigned arity = l1.arity();

    for (unsigned i = 0; i < arity; i++) {
        const term* lhs = l1.lit->arg_bases[i];
        const term* rhs = l2.arg_bases[i];
        if (!lhs->seems_possibly_unifiable(rhs, *hint)) {
            delete hint;
            return nullptr;
        }
    }
    return hint;
}

const subterm_hint* propagator_base::cache_unification(const ground_literal& l1, const indexed_literal& l2) {
    const subterm_hint* hint = unificationHints.get(l1.lit->index, l2.index);
    if (hint != nullptr)
        return hint;
    if (l1.lit->nameID == l2.nameID &&
        (hint = collect_constrain_unifiable(l1, l2)) != nullptr) {

        unificationHints.set(l1.lit->index, l2.index, hint);
        if (l2.index != l1.lit->index)
            unificationHints.set(l2.index, l1.lit->index, hint->swap());
        return hint;
    }
    unificationHints.set_invalid(l1.lit->index, l2.index);
    if (l2.index != l1.lit->index)
        unificationHints.set_invalid(l2.index, l1.lit->index);
    return FAILED_PTR;
}

string propagator_base::clause_to_string(const vector<ground_literal>& ground,
                                         unordered_map<term_instance*, string>* prettyNames) {
    if (ground.empty())
        return "false";
    if (ground.size() == 1)
        return pretty_print_literal(ground[0], prettyNames);
    stringstream sb;
    sb << '(' << pretty_print_literal(ground[0], prettyNames);
    for (int i = 1; i < ground.size(); i++) {
        sb << " || " << pretty_print_literal(ground[i], prettyNames);
    }
    sb << ')';
    return sb.str();
}

string propagator_base::pretty_print_literal(const fo_literal* l, unsigned cpyIdx,
                                             unordered_map<term_instance*, string>* prettyNames) {
    stringstream sb;
    if (!l->polarity)
        sb << "not ";
    sb << l->name;
    if (l->arity() == 0)
        return sb.str();
    sb << '(';
    sb << l->arg_bases[0]->pretty_print(cpyIdx, prettyNames);
    for (int i = 1; i < l->arity(); i++) {
        sb << ", " << l->arg_bases[i]->pretty_print(cpyIdx, prettyNames);
    }
    sb << ')';
    return sb.str();
}
