#pragma once

#include "propagator_base.h"

class fmb_propagator : public propagator_base {

    z3::sort finite_sort;
    z3::expr_vector domain;

    vector<tri_state> interpretation;

    const unsigned lvl;

    int finalCnt = 0;

public:
    fmb_propagator(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft);

    ~fmb_propagator() override;

    bool next_level() {
        progParams.depth = lvl + 1;

        if (progParams.mode == Core)
            return next_level_core();

        assert(progParams.mode == Rectangle);
        for (unsigned i = 0; i < matrix.size(); i++) {
            if (matrix[i]->Ground && progParams.multiplicity[i] > 0)
                continue;
            progParams.multiplicity[i] = progParams.depth;
        }
        return false;
    }

    inline unsigned get_final_cnt() const {
        return finalCnt;
    }

    void check_proof(z3::context& ctx);

    void assert_root();

    void fixed(literal e, bool value);

    void final() override;

    void print_proof(unordered_map<term_instance*, string>& prettyNames, unordered_map<unsigned, int>& usedClauses) {
        std::cout << "Outputting model TBD" << std::endl;
        std::flush(std::cout);
    }

};
