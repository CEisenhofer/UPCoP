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

propagator_base::propagator_base(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned timeLeft)
    : z3Propagator(progParams.smt ? z3_propagator::create(this, timeLeft) : nullptr), cadicalPropagator(!progParams.smt ? new CaDiCal_propagator(this, timeLeft) : nullptr),
    term_solver(adtSolver), m(z3Propagator != nullptr ? z3Propagator->m : cadicalPropagator->m), generator(0), progParams(progParams), matrix(cnf)
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


clause_instance* propagator_base::create_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector) {
    vector<ground_literal> instances;
    instances.reserve(clause->literals.size());
    for (auto* lit : clause->literals) {
        instances.emplace_back(lit, cpyIdx);
    }
    return new clause_instance(clause, cpyIdx, selector, std::move(instances));
}
