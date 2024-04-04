#include "fmb_propagator.h"

fmb_propagator::fmb_propagator(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams,
                               unsigned literalCnt, unsigned timeLeft) :
        propagator_base(cnf, adtSolver, progParams, timeLeft),
        domain(z3Propagator->get_ctx()),
        finite_sort(z3Propagator->get_ctx().uninterpreted_sort("FM")),
        lvl(progParams.depth) {

    assert(progParams.smt);
    assert(z3Propagator != nullptr);
    interpretation.resize()

    for (unsigned i = 0; i < progParams.depth; i++) {
        domain.push_back(z3Propagator->get_ctx().constant(("var" + std::to_string(i + 1)).c_str(), finite_sort));
    }
}

fmb_propagator::~fmb_propagator() {
}

void fmb_propagator::check_proof(z3::context& ctx) {
    std::cout << "Check model TBD" << std::endl;
    std::flush(std::cout);
}

void fmb_propagator::assert_root() {
    z3Propagator->get_solver().add(z3::distinct(domain));
}

void fmb_propagator::fixed(literal_term* e, bool value) {
}

void fmb_propagator::final() {

    for (unsigned i = 0; i < matrix.size(); i++) {
        auto& clause = matrix[i];
        vector<unsigned> assignmentStack;
        assignmentStack.reserve(clause->variables.size());
        while (true) {
            for (unsigned j = assignmentStack.size(); j < clause->variables.size(); j++) {
                assignmentStack.push_back(0);
            }
            for (unsigned j = 0; j < clause->size(); j++) {

            }
            for (unsigned j = (unsigned)assignmentStack.size() && assignmentStack.back() == progParams.depth - 1; j > 0; j--) {
                assignmentStack.pop_back();
            }
            if (assignmentStack.empty())
                break;
            assert(assignmentStack.back() < progParams.depth);
            assignmentStack.back()++;
        }
    }

}
