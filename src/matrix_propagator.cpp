#include "matrix_propagator.h"

constexpr unsigned MAX_FINAL_STEPS = 10000;
constexpr unsigned MAX_FINAL_PATHS = 1;

matrix_propagator::matrix_propagator(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft) :
        propagator_base(cnf, adtSolver, progParams, literalCnt, timeLeft), lvl(progParams.depth) {

    assert(progParams.mode == Rectangle || progParams.mode == Core);

    cachedClauses.resize(matrix.size());

    create_instances();

    if (progParams.mode == Core) {
        for (unsigned i = 0; i < matrix.size(); i++) {
            if (matrix[i]->Ground && progParams.multiplicity[i] > 0) {
                clauseLimitListExpr.push_back(m.mk_true());
                continue;
            }
            clauseLimitListExpr.push_back(m.mk_lit(new_observed_var(OPT("limit#" + to_string(i)))));
            clauseLimitMap.insert(make_pair(clauseLimitListExpr[i], i));
        }

        for (int i = 0; i < matrix.size(); i++) {
            if (matrix[i]->Ground && progParams.multiplicity[i] > 0)
                continue;
            assume(clauseLimitListExpr[i]);
        }
    }
}

matrix_propagator::~matrix_propagator() {
    for (auto& clause : allClauses) {
        delete clause;
    }
}

void matrix_propagator::create_instances() {
    for (unsigned i = 0; i < progParams.multiplicity.size(); i++) {
        assert(progParams.multiplicity[i] <= 1 || !matrix[i]->Ground);
        if (progParams.multiplicity[i] == 0)
            continue;
        get_ground(matrix[i], progParams.multiplicity[i] - 1);
    }
}

static int callCnt = 0;

bool matrix_propagator::next_level_core() {
    // Try to minimize the core by brute force

    std::vector<unsigned> required;
    std::vector<unsigned> unknown;
    std::vector<unsigned> notFailed;
    tri_state res = tri_state::unsat;

    for (unsigned i = 0; i < clauseLimitListExpr.size(); i++) {
        if (clauseLimitListExpr[i] != m.mk_true())
            unknown.push_back(i);
    }

    while (!unknown.empty()) {
        notFailed.clear();
        if (res == unsat) {
            Log("Core contains: ");

            for (unsigned j = unknown.size(); j > 0; j--) {
                unsigned c = unknown[j - 1];
                assert(!clauseLimitListExpr[c]->is_true());
                if (!failed(clauseLimitListExpr[c])) {
                    notFailed.push_back(c);
                    std::swap(unknown[j - 1], unknown.back());
                    unknown.pop_back();
                }
            }

            for (unsigned j = 0; j < unknown.size(); j++) {
                Log("#" << unknown[j]);
                if (j < unknown.size() - 1)
                    Log(", ");
            }
            LogN("");

            // Problematic; keep out for now...
            /*for (unsigned c: notFailed) {
                solver->clause((signed) clauseLimitListExpr[c]->get_lit());
            }*/
        }

        if (unknown.empty())
            break;

        for (unsigned i = 0; i < unknown.size() - 1; i++) {
            assume(clauseLimitListExpr[unknown[i]]);
        }

        LogN("Trying to eliminate #" << unknown.back());

        callCnt++;
        res = check();
        const unsigned currentClause = unknown.back();
        unknown.pop_back();
        if (res != unsat) {
            LogN("Limit #" << currentClause << " required");
            required.push_back(currentClause);
            add_assertion(clauseLimitListExpr[currentClause]);
        }
        else {
            LogN("Limit #" << currentClause << " redundant");
        }
    }

    if (required.empty())
        return true;

    Log("Minimal core: ");

    for (unsigned j = 0; j < required.size(); j++) {
        Log("#" << required[j]);
        if (j < required.size() - 1)
            Log(", ");
    }
    LogN("");

    for (unsigned c : required) {
        progParams.priority[c]++;
    }

    unsigned maxVar = 1;
    unsigned maxValue = 0;
    for (unsigned v : required) {
        if (progParams.priority[v] > maxValue) {
            maxVar = v;
            maxValue = progParams.priority[v];
        }
    }

    progParams.priority[maxVar] = 0;
    progParams.multiplicity[maxVar]++;
    assert(progParams.multiplicity[maxVar] <= 1 || !matrix[maxVar]->Ground);
    LogN("Increase clause #" + to_string(maxVar) + " to " + to_string(progParams.multiplicity[maxVar]));
    return false;
}

clause_instance* matrix_propagator::create_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector) {
    vector<ground_literal> instances;
    instances.reserve(clause->literals.size());
    for (auto* lit : clause->literals) {
        instances.emplace_back(lit, cpyIdx);
    }
    return new clause_instance(clause, cpyIdx, selector, std::move(instances));
}

bool matrix_propagator::are_same_atom(const ground_literal& l1, const ground_literal& l2) {
    if (l1.arity() != l2.arity())
        return false;
    const auto* unification = cache_unification(l1, l2);
    assert(unification != nullptr);
    if (large_array::is_invalid(unification))
        return false;
    bool res = unification->is_satisfied(*this, l1, l2);
    assert(res == unificationHints.get(l2.lit->Index, l1.lit->Index)->is_satisfied(*this, l2, l1));
    return res;
}


void matrix_propagator::check_proof(z3::context& ctx) {
    if (!progParams.checkProof)
        return;

    z3::solver z3Solver(ctx);

    unordered_map<term_instance*, optional<z3::expr>> lookup;
    vector<term_instance*> allTerms;
    z3::expr_vector clauses(ctx);

    for (clause_instance* c : chosen) {
        assert(c->value == sat);
        vector<term_instance*> terms;
        z3::expr_vector literal(ctx);

        for (ground_literal l : c->literals) {
            z3::expr_vector args(ctx);
            z3::sort_vector argSorts(ctx);
            for (const term* t : l.lit->arg_bases) {
                term_instance* inst = t->get_instance(l.copyIdx, *this);
                terms.push_back(inst);
                args.push_back(inst->to_z3_adt(*this, ctx, lookup, allTerms));
                argSorts.push_back(inst->t->solver.get_z3_adt_sort());
            }
            z3::expr e = ctx.function(l.lit->name.c_str(), argSorts, ctx.bool_sort())(args);
            if (!l.lit->polarity)
                e = !e;
            literal.push_back(e);
        }

        clauses.push_back(mk_or(literal));
    }

    for (unsigned i = 0; i < allTerms.size(); i++) {
        term_instance* pair = allTerms[i];
        if (pair->is_root() || !(pair->t->is_var()))
            continue;
        z3Solver.add(pair->to_z3_adt(*this, ctx, lookup, allTerms) == pair->find_root(*this)->to_z3_adt(*this, ctx, lookup, allTerms));
    }


    z3::check_result res = z3Solver.check();
    if (res != z3::check_result::sat) {
        cout << "Could not verify consistency of connections" << endl;
        exit(130);
    }
    for (auto clause : clauses) {
        z3Solver.add(clause);
    }

#ifndef NDEBUG
    auto assertions = z3Solver.assertions();
    for (unsigned i = 0; i < assertions.size(); i++) {
        std::cout << "Assertion: " << assertions[i] << std::endl;
    }
#endif

    res = z3Solver.check();
    if (res != z3::check_result::unsat) {
        cout << "Could not verify proof" << endl;
        exit(130);
    }
    cout << "Proof verified successful!" << endl;
}

clause_instance* matrix_propagator::get_ground(const indexed_clause* clause, unsigned cpy) {
    if (clause == nullptr)
        return nullptr;
    auto& instances = cachedClauses[clause->Index];
    for (unsigned i = instances.size(); i <= cpy; i++) {
        literal selector = m.mk_lit(new_observed_var(OPT("select#" + to_string(clause->Index) + "@" + to_string(i))));
        auto* info = create_clause_instance(clause, i, selector);
        instances.push_back(info);
        allClauses.push_back(info);
        assert(!contains_key(exprToInfo, selector));
        exprToInfo.insert(make_pair(selector, info));
    }
    return instances[cpy];
}

void matrix_propagator::assert_root() {
    assert(std::any_of(matrix.clauses.begin(), matrix.clauses.end(),
                       [](const indexed_clause* c) { return c->Conjecture; }));
    vector<literal> root;
    for (unsigned i = 0; i < matrix.size(); i++) {
        if (matrix[i]->Conjecture) {
            root.push_back(get_ground(matrix[i], 0)->selector);
#ifdef DIMACS
            dimacs << root.back().get_lit() << " ";
#endif
        }
    }
    add_assertion(std::move(root));

#ifdef DIMACS
    dimacs << "0\n";
#endif

    if (z3Propagator != nullptr && progParams.mode == Rectangle) {
        z3::expr_vector rootExpr(z3Propagator->get_ctx());

        rootExpr.resize(allClauses.size());
        for (unsigned i = 0; i < allClauses.size(); i++) {
            z3::expr e = allClauses[i]->selector->get_z3(*z3Propagator);
            rootExpr.set(i, e);
        }
        z3Propagator->add_assertion(z3::atleast(rootExpr, lvl));
        z3Propagator->add_assertion(z3::atmost(rootExpr, lvl));
    }
}

void matrix_propagator::pb_clause_limit() {
    if (cadicalPropagator == nullptr || progParams.mode != Rectangle || pbPropagated)
        return;

    start_watch(pb_time);
    static justification just;
    static vector<literal> prop;

    bool upperLimit = chosen.size() == lvl;
    bool lowerLimit = allClauses.size() - not_chosen.size() == lvl;
    assert(!(upperLimit && lowerLimit));

    if (upperLimit) {
        LogN("Enforcing upper limit");
        pbPropagated = true;
        add_undo([this]() { pbPropagated = false; });
        just.clear();
        prop.clear();
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause : allClauses) {
            if (clause->value == sat)
                just.push_literal(clause->selector);
            else if (clause->value == undef)
                prop.push_back(m.mk_not(clause->selector));
        }

        for (auto* p : prop) {
            if (!soft_propagate(just, p))
                return;
        }
    }
    else if (lowerLimit) {
        LogN("Enforcing lower limit");
        pbPropagated = true;
        add_undo([this]() { pbPropagated = false; });
        just.clear();
        prop.clear();
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause : allClauses) {
            if (clause->value == unsat)
                just.push_literal(m.mk_not(clause->selector));
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p : prop) {
            if (!soft_propagate(just, p))
                return;
        }
    }
    stop_watch(pb_time);
}

void matrix_propagator::fixed(literal_term* e, bool value) {
    try {

        if (value && false) {
            for (const auto& [just, c1, c2] : e->connections) {
                bool val = false;
                if (get_value(just, val) && val) {
                    auto* r1 = c1->find_root(*this);
                    auto* r2 = c2->find_root(*this);
                    auto* start = chosen[0]->find_root(*this);

                    if (r1 == r2)
                        continue;
                    vector<clause_instance*> toEnable;
                    if (r1 == start) {
                        auto* current = r2;
                        do {
                            toEnable.push_back(current);
                            current = current->next_sibling;
                        } while (current != r2);
                    }
                    else if (r2 == start) {
                        auto* current = r1;
                        do {
                            toEnable.push_back(current);
                            current = current->next_sibling;
                        } while (current != r1);
                    }
                    clause_instance::merge_root(r1, r2, *this);
                    for (auto* c : toEnable) {
                        if (!delayed_rp(c))
                            return;
                    }
                }
            }
        }


        if (is_skip(e))
            return;

        if (term_solver.asserted(e, value))
            return;

        clause_instance* info = nullptr;
        if (!tryGetValue(exprToInfo, e, info)) {
            int lim = 0;
            if (value)
                return;
            if (!hasLimFalse && tryGetValue(clauseLimitMap, e, lim)) {
                hasLimFalse = true;
                add_undo([this]() { hasLimFalse = false; });
            }
            return;
        }

        if (!value) {
            info->value = unsat;
            not_chosen.push_back(info);
            add_undo([&]() {
                not_chosen.back()->value = undef;
                not_chosen.pop_back();
            });
            pb_clause_limit();
            return;
        }

        unsigned c = info->clause->Index;

        /*for (unsigned i = info->copy_idx; i > 0; i--) {
            if (cachedClauses[c][i - 1]->value == sat)
                break; // If some smaller element is already assigned true, it has propagated the remaining ones already - no reason to continue
            propagate({ e }, GetGround(info->clause, i - 1)->selector);
        }*/

        if (info->copyIdx > 0) {
            auto val = cachedClauses[c][info->copyIdx - 1]->value;
            if (val != sat) {
                justification just(e);
                if (!soft_propagate(just, get_ground(info->clause, info->copyIdx - 1)->selector))
                    return;
            }

#ifndef PUSH_POP
            if (z3Propagator != nullptr || !info->propagated) {
#endif
                start_watch(var_order_time);
                stack<less_than> stack;
                for (unsigned i = info->clause->variables.size(); i > 0; i--) {
                    term* var = info->clause->variables[i - 1];
                    stack.emplace(var->get_instance(info->copyIdx, *this),  var->get_instance(info->copyIdx - 1, *this));
                }
                bool eq = false;
                std::vector<less_than> subproblems;
                term_solver.preprocess_less(std::move(stack), subproblems, eq);
                assert(!subproblems.empty());
                formula expr = term_solver.make_less_expr(subproblems, eq);
                justification just(e);
                hard_propagate(just, expr); // don't remove justification
                stop_watch(var_order_time);
#ifndef PUSH_POP
            }
#endif
        }

        info->value = sat;
        chosen.push_back(info);
        add_undo([&]() {
            chosen.back()->value = undef;
            chosen.pop_back();
        });

        if (!delayed_rp(info))
            return;

#ifndef PUSH_POP
        if (z3Propagator != nullptr || !info->propagated) {
#endif
            start_watch(tautology_time);
            // Tautology elimination
            for (int k = 0; k < info->literals.size(); k++) {
                for (int l = k + 1; l < info->literals.size(); l++) {
                    if (info->literals[k].lit->polarity != info->literals[l].lit->polarity &&
                        info->literals[k].lit->nameID == info->literals[l].lit->nameID) {

                        // TODO: Store tautology constraints
                        auto* diseq = collect_constrain_unifiable(info->literals[k], *(info->literals[l].lit));
                        if (diseq == nullptr)
                            continue;
                        // Clause contains two complementary literals
                        // Why did the simplifier not remove those?!
                        if (diseq->tautology()) {
                            LogN("Detected tautology clause - get a better preprocessor: " << info->clause->to_string());
                            // assert(false);
                        }
                        // clause->TautologyConstraints->emplace_back(k, l, diseq);

                        formula neq = diseq->get_neg_constraints(*this, info->literals[k], info->literals[l]);
                        if (!neq->is_true()) {
                            justification just(e);
                            hard_propagate({ e }, neq); /* we need e as a justification; otherwise a tautology clause would result in a root conflict */
                        }
                        delete diseq;
                    }
                }
            }
            stop_watch(tautology_time);

            if (!propagate_rules(e, info))
                return;
#ifndef PUSH_POP
            info->propagated = true;
        }
#endif

        pb_clause_limit();
    }
    catch (z3::exception& ex) {
        cout << "Crashed Z3: " << ex.msg() << endl;
        __builtin_trap();
        exit(131);
    }
    catch (...) {
        cout << "Crashed" << endl;
        __builtin_trap();
        exit(131);
    }
}

bool matrix_propagator::delayed_rp(clause_instance* info) {
    /*if (chosen[0]->find_root(*this) != info->find_root(*this))
        // The current clause is not connected to a relevant clause
        return;*/

    if (!is_smt()) {
        // "Relevance propagation" of delayed equalities
        for (const auto& eq : info->delayedRelevantTrue) {
            if (eq.RHS->origin != nullptr) {
                if (eq.RHS->origin->value == unsat)
                    continue;
                if (eq.RHS->origin->value == undef) {
                    eq.RHS->origin->delayedRelevantTrue.push_back(eq);
                    add_undo([eq]() { eq.RHS->origin->delayedRelevantTrue.pop_back(); });
                    continue;
                }
            }
            try {
                assert(
                        (is_smt() && eq.just.litJust.empty() && eq.just.eqJust.size() == 1 && eq.just.diseqJust.first == nullptr) ||
                        (!is_smt() && eq.just.litJust.size() == 1 && eq.just.eqJust.empty() && eq.just.diseqJust.first == nullptr));
                LogN("Delayed: " << eq.to_string() << " := 1");
                if (!term_solver.asserted_eq(eq.just, eq.LHS, eq.RHS, true))
                    return false;
            }
            catch (...) {
                cout << "Crashed unify" << endl;
                exit(132);
            }
        }
        for (const auto& eq : info->delayedRelevantFalse) {
            if (eq.RHS->origin != nullptr) {
                if (eq.RHS->origin->value == unsat)
                    continue;
                if (eq.RHS->origin->value == undef) {
                    eq.RHS->origin->delayedRelevantFalse.push_back(eq);
                    add_undo([eq]() { eq.RHS->origin->delayedRelevantFalse.pop_back(); });
                    continue;
                }
            }
            try {
                assert(
                        (is_smt() && eq.just.litJust.empty() && eq.just.eqJust.empty() && eq.just.diseqJust.first != nullptr) ||
                        (!is_smt() && eq.just.litJust.size() == 1 && eq.just.eqJust.empty() && eq.just.diseqJust.first == nullptr));
                LogN("Delayed: " << eq.to_string() << " := 0");
                if (!term_solver.asserted_eq(eq.just, eq.LHS, eq.RHS, false))
                    return false;
            }
            catch (...) {
                cout << "Crashed unify" << endl;
                exit(132);
            }
        }
    }
    for (const auto& less : info->delayedRelevantLess) {
        if (less.RHS->origin != nullptr) {
            if (less.RHS->origin->value == unsat)
                continue;
            if (less.RHS->origin->value == undef) {
                less.RHS->origin->delayedRelevantLess.push_back(less);
                add_undo([less]() { less.RHS->origin->delayedRelevantLess.pop_back(); });
                continue;
            }
        }
        try {
            LogN("Delayed: " << less.to_string());
            literal lit = term_solver.make_less_atom(less.LHS, less.RHS);

            if (!term_solver.asserted_less(lit, less.LHS, less.RHS))
                return false;
        }
        catch (...) {
            cout << "Crashed unify" << endl;
            exit(132);
        }
    }
    return true;
}

formula_term* matrix_propagator::connect_literal(literal just, clause_instance* info, const ground_literal& lit) {
    // TODO: Only propagate the 0th copy if the clause is ground
    vector<formula> exprs;
    for (auto& cachedClause : cachedClauses) {
        assert(progParams.mode == Core || !cachedClause.empty());
        if (cachedClause.empty())
            continue;
        unsigned literalCnt = cachedClause[0]->literals.size();
        for (int j = 0; j < literalCnt; j++) {
            // TODO: Only iterate over the relevant ones
            const subterm_hint* unification = cache_unification(lit, cachedClause[0]->literals[j]);

            if (large_array::is_invalid(unification) ||
                lit.lit->polarity == cachedClause[0]->literals[j].lit->polarity)
                continue;

            for (int k = 0; k < cachedClause.size(); k++) {
                auto* clause = cachedClause[k];
                if (clause == info)
                    continue; // We don't want to connect to itself...
                vector<formula> constraints = { cachedClause[k]->selector };
                unification->get_pos_constraints(*this, lit, cachedClause[k]->literals[j], constraints);
                formula conj = m.mk_and(constraints);
                [[unlikely]]
                if (conj->is_true())
                    return m.mk_true();
                formula_term::connection_tseitin connectionTseitin;
                connectionTseitin.sideCondition = just;
                connectionTseitin.c1 = info;
                connectionTseitin.c2 = cachedClause[k];
                conj->connections.push_back(connectionTseitin);
                exprs.push_back(conj);
            }
        }
    }

    if (progParams.mode == Core) {
        for (int i = 0; i < matrix.size(); i++) {
            for (int j = 0; j < matrix[i]->size(); j++) {
                const subterm_hint* unification = cache_unification(lit, *matrix[i]->literals[j]);
                if (large_array::is_invalid(unification) || lit.lit->polarity == matrix[i]->literals[j]->polarity)
                    continue;
                if (!cachedClauses[i].empty() && matrix[i]->Ground) {
                    assert(cachedClauses[i].size() == 1);
                    continue;
                }

                exprs.push_back(
                        !cachedClauses[i].empty()
                        ? m.mk_and({
                                           cachedClauses[i].back()->selector,
                                           m.mk_not(clauseLimitListExpr[i]),
                                   }, true)
                        : m.mk_not(clauseLimitListExpr[i])
                );
                break;
            }
        }
    }

    return m.mk_or(exprs);
}

void matrix_propagator::final() {

    if (hasLimFalse)
        // Used for unsat core minimization - this is a senseless state anyway...
        return;

    finalCnt++;

    z3Propagator->debug = finalCnt == 2;
    if (z3Propagator->debug) {
        LogN("Buggy final");
    }

    start_watch(final_time);
    assert(!chosen.empty());
    assert(progParams.mode != Rectangle || chosen.size() == lvl);

    vector<vector<vector<path_element>>> submatrix_paths;
    LogN("Final (" << finalCnt << ")");

    if (false) {
        unordered_set<clause_instance*> visited;
        unsigned minPathCnt = UINT_MAX;

        for (unsigned i = 0; i < chosen.size(); i++) {
            clause_instance* const start = chosen[i];
            if (contains(visited, start->find_root(*this)))
                continue;
            submatrix_paths.emplace_back();
            visited.insert(start->find_root(*this));
            clause_instance* current = start;
            vector<clause_instance*> shuffledChosen;

            do {
                shuffledChosen.push_back(current);
                current = current->next_sibling;
            } while (current != start);

            Shuffle(shuffledChosen);

            vector<path_element> current_path;
            unsigned steps = 0;

            find_path(0, shuffledChosen, current_path, submatrix_paths.back(), steps);
            if (submatrix_paths.back().empty() && steps >= MAX_FINAL_STEPS) {
                find_path_sat(shuffledChosen, submatrix_paths.back());
            }
            if (submatrix_paths.back().empty())
                return;
            minPathCnt = min(minPathCnt, (unsigned)submatrix_paths.back().size());
#ifdef DEBUG
            LogN("Found at least: " << submatrix_paths.back().size());
#endif
        }
        LogN("Found " << submatrix_paths.size() << " separate submatrixes");

        if (submatrix_paths.size() > 1) {
            // TODO: Remove; just want to see if this occurs in practice
            LogN("Created multiple submatrixes");
        }
        assert(minPathCnt > 0 && minPathCnt != UINT_MAX);

        // just randomly put them together again
        vector<vector<path_element>> combinedPaths;
        [[unlikely]]
        if (submatrix_paths.size() != 1 && progParams.mode == Rectangle) {
            combinedPaths.reserve(minPathCnt);
            for (unsigned i = 0; i < minPathCnt; i++) {
                combinedPaths.emplace_back();
                for (unsigned j = 0; j < submatrix_paths.size(); j++) {
                    auto randomPath = submatrix_paths[j][get_random(0, submatrix_paths[j].size())];
                    for (unsigned k = 0; k < randomPath.size(); k++) {
                        combinedPaths.back().push_back(randomPath[k]);
                    }
                }
            }
            submatrix_paths.resize(0);
            submatrix_paths.push_back(std::move(combinedPaths));
        }
    }
    else {
        submatrix_paths.emplace_back();
        vector<clause_instance*> shuffledChosen(chosen);

        Shuffle(shuffledChosen);

        vector<path_element> current_path;
        unsigned steps = 0;

        find_path(0, shuffledChosen, current_path, submatrix_paths.back(), steps);
        if (submatrix_paths.back().empty() && steps >= MAX_FINAL_STEPS) {
            find_path_sat(shuffledChosen, submatrix_paths.back());
        }
        if (submatrix_paths.back().empty())
            return;
#ifdef DEBUG
        LogN("Found at least: " << submatrix_paths.back().size());
#endif
    }

    for (const auto& paths : submatrix_paths) {
        justification just(paths.size());
        for (int i = 0; i < paths[0].size(); i++) {
            just.push_literal(paths[0][i].clause.selector);
        }

        for (const auto& path : paths) {
            vector<formula> constraints;
            for (int i = 0; i < path.size(); i++) {
                for (int j = i + 1; j < path.size(); j++) {
                    assert(!are_connected(path[i].lit, path[j].lit));
                    vector<formula> unificationConstraint;
                    const auto* unification = unificationHints.get(path[i].lit.lit->Index, path[j].lit.lit->Index);
                    assert(unification != nullptr);
                    if (!large_array::is_invalid(unification) && path[i].lit.lit->polarity != path[j].lit.lit->polarity) {
                        unification->get_pos_constraints(*this, path[i].lit, path[j].lit, unificationConstraint);
                        if (!unificationConstraint.empty()) {
                            constraints.push_back(m.mk_and(unificationConstraint));
                            LogN(m.mk_and(unificationConstraint)->to_string());
                        }
                    }
                }
            }

            if (progParams.mode == Core) {
                for (auto elem : path) {
                    for (unsigned i = 0; i < matrix.size(); i++) {
                        indexed_clause* cl = matrix[i];
                        unsigned literalCnt = cl->literals.size();
                        for (int j = 0; j < literalCnt; j++) {

                            const subterm_hint* unification = cache_unification(elem.lit, *(cl->literals[j]));

                            if (large_array::is_invalid(unification) ||
                                elem.lit.lit->polarity == cl->literals[j]->polarity)
                                continue;

                            unsigned maxId = 0;
                            auto& cachedClause = cachedClauses[i];
                            for (; maxId < cachedClause.size(); maxId++) {
                                if (submatrix_paths.size() == 1) {
                                    if (cachedClause[maxId]->value != sat)
                                        break;
                                }
                                else {
                                    // TODO: Do something smarter here to detect what is the smallest index that does not belong to the submatrix
                                    clause_instance* current = cachedClause[maxId];
                                    if (all_of(path.begin(), path.end(), [current](const path_element& e) { return &e.clause != current; }))
                                        break;
                                }
                            }
                            if (maxId >= cachedClause.size()) {
                                constraints.push_back(m.mk_not(clauseLimitListExpr[i]));
                            }
                            else {
                                vector<formula> cnstr = { cachedClause[maxId]->selector };
                                unification->get_pos_constraints(*this, elem.lit, cachedClause[maxId]->literals[j], cnstr);
                                constraints.push_back(m.mk_and(cnstr));
                            }
                        }
                    }
                }
            }
            if (constraints.empty()) {
                propagate_conflict(just);
                return;
            }
            hard_propagate(just, m.mk_or(constraints));
        }
    }
    if (z3Propagator->debug)
        exit(-11);
}

void matrix_propagator::find_path(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path, vector<vector<path_element>>& foundPaths, unsigned& steps) {
    if (clauseIdx >= clauses.size()) {
        foundPaths.push_back(path);
#ifndef NDEBUG
        for (int i = 0; i < path.size(); i++) {
            for (int j = i + 1; j < path.size(); j++) {
                assert(!are_connected(path[i].lit, path[j].lit));
            }
        }
#endif
        return;
    }

    clause_instance* info = clauses[clauseIdx];
    vector<int> order;
    order.resize(info->literals.size());
    for (int i = 0; i < order.size(); i++) {
        order[i] = i;
    }

    Shuffle(order);

    assert(!info->literals.empty());
    for (int v : order) {
        auto l1 = info->literals[v];
        bool failed = false;

        for (const path_element& elem : path) {
            if (are_connected(l1, elem.lit)) {
                failed = true;
                break;
            }
        }

        if (failed)
            continue;

        path.emplace_back(*info, l1);
        steps++;
        find_path(clauseIdx + 1, clauses, path, foundPaths, steps);
        if (foundPaths.size() >= MAX_FINAL_PATHS)
            return;
        if (steps >= MAX_FINAL_STEPS)
            return;
        path.pop_back();
    }
}

void matrix_propagator::find_path_sat(const vector<clause_instance*>& clauses, vector<vector<path_element>>& foundPaths) {
    vector<ground_literal> literals;
    vector<vector<int>> sat_clauses;
    CaDiCaL::Solver subsolver;
    do {
        for (clause_instance* cl : clauses) {
            sat_clauses.emplace_back();
            sat_clauses.back().reserve(cl->literals.size());
            for (auto lit : cl->literals) {

                int i = 0;
                for (; i < literals.size(); i++) {
                    if (are_same_atom(lit, literals[i]))
                        break;
                }
                if (i >= literals.size())
                    literals.push_back(lit);
                int sat_lit = (i + 1) * (lit.lit->polarity ? 1 : -1);
                sat_clauses.back().push_back(sat_lit);
                subsolver.add(sat_lit);
            }
            subsolver.add(0);
        }
        int res = subsolver.solve();
        if (res == 20)
            return;

        foundPaths.emplace_back();
        foundPaths.back().reserve(clauses.size());
        vector<int> newClause;
        newClause.reserve(clauses.size());

        for (unsigned i = 0; i < clauses.size(); i++) {
            unsigned j = 0;
            for (; j < clauses[i]->literals.size(); j++) {
                int val = subsolver.val(abs(sat_clauses[i][j]));
                if (val == sat_clauses[i][j]) {
                    foundPaths.back().emplace_back(*clauses[i], clauses[i]->literals[j]);
                    newClause.push_back(-sat_clauses[i][j]);
                    break;
                }
            }
            assert(j < clauses[i]->literals.size());
        }

        for (int lit : newClause) {
            subsolver.add(lit);
        }
        subsolver.add(0);

    } while (foundPaths.size() < MAX_FINAL_PATHS);
}
