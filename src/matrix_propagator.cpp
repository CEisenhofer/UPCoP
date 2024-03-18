﻿#include "matrix_propagator.h"

matrix_propagator::matrix_propagator(cnf<indexed_clause*>& cnf, complex_adt_solver& adtSolver, ProgParams& progParams, unsigned literalCnt, unsigned timeLeft) :
        propagator_base(cnf, adtSolver, progParams, literalCnt, timeLeft), lvl(progParams.Depth) {

    assert(progParams.Mode == Rectangle || progParams.Mode == Core);

    cachedClauses.resize(matrix.size());

    create_instances();

    if (progParams.Mode == Core) {
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
            const int ass = clauseLimitListExpr[i]->get_lit();
            solver->assume(ass);
        }
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
    bool unsat = true;

    for (unsigned i = 0; i < clauseLimitListExpr.size(); i++) {
        if (!clauseLimitListExpr[i]->is_true())
            unknown.push_back(i);
    }

    while (!unknown.empty()) {
        notFailed.clear();
        if (unsat) {
            Log("Core contains: ");

            for (unsigned j = unknown.size(); j > 0; j--) {
                unsigned c = unknown[j - 1];
                assert(!clauseLimitListExpr[c]->is_true());
                if (!solver->failed(clauseLimitListExpr[c]->get_lit())) {
                    notFailed.push_back(c);
                    std::swap(unknown[c], unknown.back());
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
            solver->assume((signed)clauseLimitListExpr[unknown[i]]->get_lit());
        }

        LogN("Trying to eliminate #" << unknown.back());

        callCnt++;
        int res = solver->solve();
        unsat = res == 20;
        const unsigned currentClause = unknown.back();
        unknown.pop_back();
        if (!unsat) {
            LogN("Limit #" << currentClause << " required");
            required.push_back(currentClause);
            solver->clause((signed)clauseLimitListExpr[currentClause]->get_lit());
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

bool matrix_propagator::are_connected(const ground_literal& l1, const ground_literal& l2) {
    if (l1.lit->polarity == l2.lit->polarity || l1.arity() != l2.arity())
        return false;
    const auto* unification = unificationHints.get(l1.lit->Index, l2.lit->Index);
    assert(unification != nullptr);
    if (large_array::is_invalid(unification))
        return false;
    bool res = unification->IsSatisfied(*this, l1, l2);
    assert(res == unificationHints.get(l2.lit->Index, l1.lit->Index)->IsSatisfied(*this, l2, l1));
    return res;
}

void matrix_propagator::check_proof(z3::context& ctx) {
    if (!progParams.CheckProof)
        return;

    z3::solver z3Solver(ctx);

    unordered_map<term_instance*, optional<z3::expr>> lookup;
    z3::expr_vector clauses(ctx);

    for (clause_instance* c : chosen) {
        assert(c->value == sat);
        vector<term_instance*> terms;
        z3::expr_vector literal(ctx);

        for (ground_literal l : c->literals) {
            z3::expr_vector args(ctx);
            z3::sort_vector argSorts(ctx);
            for (term* t : l.lit->arg_bases) {
                term_instance* inst = t->get_instance(l.copyIdx, *this);
                terms.push_back(inst);
                args.push_back(inst->to_z3(*this, ctx, lookup));
                argSorts.push_back(inst->t->Solver.get_z3_sort());
            }
            z3::expr e = ctx.function(l.lit->name.c_str(), argSorts, ctx.bool_sort())(args);
            if (!l.lit->polarity)
                e = !e;
            literal.push_back(e);
        }

        clauses.push_back(mk_or(literal));
    }

    for (auto& pair : lookup) {
        if (pair.first->is_root() || !(pair.first->t->is_var()))
            continue;
        z3Solver.add(*(pair.second) == pair.first->find_root(*this)->to_z3(*this, ctx, lookup));
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
    for (unsigned i = 0; i < matrix.size(); i++) {
        if (matrix[i]->Conjecture) {
            int lit = get_ground(matrix[i], 0)->selector->get_lit();
            solver->add(lit);
#ifdef DIMACS
            dimacs << lit << " ";
#endif
        }
    }
    solver->add(0);

#ifdef DIMACS
    dimacs << "0\n";
#endif
}

void matrix_propagator::pb_clause_limit() {
    if (progParams.Mode != Rectangle || pbPropagated)
        return;

    static vector<literal> just;
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
        just.reserve(chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause : allClauses) {
            if (clause->value == sat)
                just.push_back(clause->selector);
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
        just.reserve(not_chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause : allClauses) {
            if (clause->value == unsat)
                just.push_back(m.mk_not(clause->selector));
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p : prop) {
            if (!soft_propagate(just, p))
                return;
        }
    }
}

void matrix_propagator::fixed(literal_term* e, bool value) {
    if (is_conflict_flag)
        return;
    try {
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
                if (!soft_propagate({ e }, get_ground(info->clause, info->copyIdx - 1)->selector))
                    return;
            }

#ifndef PUSH_POP
            if (!info->propagated) {
#endif
                stack<less_than> stack;
                for (unsigned i = info->clause->variables.size(); i > 0; i--) {
                    term* var = info->clause->variables[i - 1];
                    stack.emplace(var->get_instance(info->copyIdx, *this),  var->get_instance(info->copyIdx - 1, *this));
                }
                bool eq = false;
                std::vector<less_than> subproblems;
                bool res = term_solver.preprocess_less(std::move(stack), subproblems, eq);
                assert(res);
                assert(!subproblems.empty());
                assert(!eq);
                formula expr = term_solver.make_less_expr(subproblems, eq);
                hard_propagate({ e }, expr);
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

        // "Relevance propagation" of delayed equalities
        for (const auto& eq : info->delayedRelevantTrue) {
            try {
                assert(eq.just.litJust.size() == 1 && eq.just.eqJust.empty());
                LogN("Delayed: " << eq.to_string() << " := 1");
                if (!term_solver.asserted_eq(eq.just.litJust[0], eq.LHS, eq.RHS, true))
                    return;
            }
            catch (...) {
                cout << "Crashed unify" << endl;
                exit(132);
            }
        }
        for (const auto& eq : info->delayedRelevantFalse) {
            try {
                assert(eq.just.litJust.size() == 1 && eq.just.eqJust.empty());
                LogN("Delayed: " << eq.to_string() << " := 0");
                if (!term_solver.asserted_eq(eq.just.litJust[0], eq.LHS, eq.RHS, false))
                    return;
            }
            catch (...) {
                cout << "Crashed unify" << endl;
                exit(132);
            }
        }
        for (const auto& less : info->delayedRelevantLess) {
            try {
                LogN("Delayed: " << less.to_string());
                literal lit = term_solver.make_less_atom(less.LHS, less.RHS);

                if (!term_solver.asserted_less(lit, less.LHS, less.RHS))
                    return;
            }
            catch (...) {
                cout << "Crashed unify" << endl;
                exit(132);
            }
        }

#ifndef PUSH_POP
        if (!info->propagated) {
#endif
            // Tautology elimination
            for (int k = 0; k < info->literals.size(); k++) {
                for (int l = k + 1; l < info->literals.size(); l++) {
                    if (info->literals[k].lit->polarity != info->literals[l].lit->polarity &&
                        info->literals[k].lit->nameID == info->literals[l].lit->nameID) {

                        // TODO: Store tautology constraints
                        auto* diseq = CollectConstrainUnifiable(info->literals[k], *(info->literals[l].lit));
                        if (diseq == nullptr)
                            continue;
                        // Clause contains two complementary literals
                        // Why did the simplifier not remove those?!
                        assert(!diseq->tautology());
                        // clause->TautologyConstraints->emplace_back(k, l, diseq);

                        formula neq = diseq->GetNegConstraints(*this, info->literals[k], info->literals[l]);
                        if (!neq->is_true())
                            hard_propagate({ e }, neq);
                        delete diseq;
                    }
                }
            }

            if (!propagate_rules(e, info))
                return;
#ifndef PUSH_POP
            info->propagated = true;
        }
#endif

        pb_clause_limit();
    }
    catch (...) {
        cout << "Crashed" << endl;
        __builtin_trap();
        exit(131);
    }
}

formula_term* matrix_propagator::connect_literal(clause_instance* info, const ground_literal& lit) {
    // TODO: Only propagate the 0th copy if the clause is ground
    vector<formula> exprs;
    for (auto& cachedClause : cachedClauses) {
        assert(progParams.Mode == Core || !cachedClause.empty());
        if (cachedClause.empty())
            continue;
        unsigned literalCnt = cachedClause[0]->literals.size();
        for (int j = 0; j < literalCnt; j++) {
            // TODO: Only iterate over the relevant ones
            cache_unification(lit, cachedClause[0]->literals[j]);
            const subterm_hint* unification = unificationHints.get(
                    lit.lit->Index,
                    cachedClause[0]->literals[j].lit->Index);

            if (large_array::is_invalid(unification) ||
                lit.lit->polarity == cachedClause[0]->literals[j].lit->polarity)
                continue;

            for (int k = 0; k < cachedClause.size(); k++) {
                auto* clause = cachedClause[k];
                if (clause == info)
                    continue; // We don't want to connect to itself...
                vector<formula> constraints = { cachedClause[k]->selector };
                unification->GetPosConstraints(*this, lit, cachedClause[k]->literals[j], constraints);
                exprs.push_back(m.mk_and(constraints));
            }
        }
    }

    if (progParams.Mode == Core) {
        for (int i = 0; i < matrix.size(); i++) {
            for (int j = 0; j < matrix[i]->size(); j++) {
                cache_unification(lit, *matrix[i]->literals[j]);
                const subterm_hint* unification = unificationHints.get(lit.lit->Index, matrix[i]->literals[j]->Index);
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
                        :
                        m.mk_not(clauseLimitListExpr[i])
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

    assert(!chosen.empty());
    if (progParams.Mode == Rectangle && chosen.size() != lvl) {
        if (chosen.size() < lvl) {
            for (auto* clause : allClauses) {
                if (clause->value == undef) {
                    std::cout << "Unassigned: " << clause->clause->Index << "#" << clause->copyIdx << std::endl;
                }
            }
        }
        else {
            std::sort(chosen.begin(), chosen.end(), [](clause_instance* a, clause_instance* b) {
                if (a->clause->Index > b->clause->Index)
                    return false;
                if (a->clause->Index < b->clause->Index)
                    return true;
                if (a->copyIdx > b->copyIdx)
                    return false;
                if (a->copyIdx < b->copyIdx)
                    return true;
                return false;
            });
            for (auto* clause : chosen) {
                std::cout << "Chose ["
                          << (clause->value == tri_state::sat ? "sat" : clause->value == tri_state::unsat ? "unsat"
                                                                                                          : "unknown")
                          << "]: " << clause->clause->Index << "#" << clause->copyIdx << std::endl;
            }
        }
        assert(false);
        exit(120);
        return;
    }
    assert(progParams.Mode != Rectangle || chosen.size() == lvl);

    vector<vector<path_element>> paths;
    LogN("Final (" << ++finalCnt << ")");
    vector<clause_instance*> shuffledChosen(chosen);
    Shuffle(shuffledChosen);
    const int limit = 1;

    vector<path_element> current_path;
    find_path(0, shuffledChosen, current_path, paths, limit);
    if (paths.empty())
        return;
#ifdef DEBUG
    LogN("Found at least: " << paths.size());
#endif
    // TODO: Do we really need all selection expressions as justifications (if we have multiple of the same kind)
    vector<literal> justifications;
    justifications.reserve(chosen.size());
    for (int i = 0; i < chosen.size(); i++) {
        justifications.push_back(chosen[i]->selector);
    }

    for (auto& path : paths) {
        vector<formula> constraints;
        for (int i = 0; i < path.size(); i++) {
            for (int j = i + 1; j < path.size(); j++) {
                assert(!are_connected(path[i].lit, path[j].lit));
                vector<formula> unificationConstraint;
                const auto* unification = unificationHints.get(path[i].lit.lit->Index, path[j].lit.lit->Index);
                assert(unification != nullptr);
                if (!large_array::is_invalid(unification) && path[i].lit.lit->polarity != path[j].lit.lit->polarity) {
                    unification->GetPosConstraints(*this, path[i].lit, path[j].lit, unificationConstraint);
                    if (!unificationConstraint.empty())
                        constraints.push_back(m.mk_and(unificationConstraint));
                }
            }
        }

        if (progParams.Mode == Core) {
            for (auto elem : path) {
                for (unsigned i = 0; i < matrix.size(); i++) {
                    indexed_clause* cl = matrix[i];
                    unsigned literalCnt = cl->literals.size();
                    for (int j = 0; j < literalCnt; j++) {
                        cache_unification(elem.lit, *(cl->literals[j]));
                        const subterm_hint* unification = unificationHints.get(
                                elem.lit.lit->Index,
                                cl->literals[j]->Index);

                        if (large_array::is_invalid(unification) ||
                            elem.lit.lit->polarity == cl->literals[j]->polarity)
                            continue;

                        unsigned maxId = 0;
                        auto& cachedClause = cachedClauses[i];
                        for (; maxId < cachedClause.size(); maxId++) {
                            if (cachedClause[maxId]->value != undef)
                                break;
                        }
                        if (maxId >= cachedClause.size()) {
                            constraints.push_back(m.mk_not(clauseLimitListExpr[i]));
                        }
                        else {
                            vector<formula> cnstr = { cachedClause[maxId]->selector };
                            unification->GetPosConstraints(*this, elem.lit, cachedClause[maxId]->literals[j], cnstr);
                            cnstr.push_back(m.mk_and(cnstr));
                        }
                    }
                }
            }
        }
        if (constraints.empty()) {
            propagate_conflict(justifications);
            return;
        }
        hard_propagate(justifications, m.mk_or(constraints));
    }
}

void matrix_propagator::find_path(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path,
                                  vector<vector<path_element>>& foundPaths, int limit) {
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

        path.emplace_back(*info->clause, info->copyIdx, l1);
        find_path(clauseIdx + 1, clauses, path, foundPaths, limit);
        if (foundPaths.size() >= limit)
            return;
        path.pop_back();
    }
}

literal matrix_propagator::decide() {
    /*for (unsigned i = 0; i < cachedClauses.size(); i++) {
        for (unsigned j = 0; j < cachedClauses[i].size(); j++) {
            if (cachedClauses[i][j]->value == unsat)
                break;
            if (cachedClauses[i][j]->value == undef) {
                return cachedClauses[i][j]->selector;
            }
        }
    }*/
    return m.mk_false();
}
