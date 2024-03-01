#include "matrix_propagator.h"

matrix_propagator::matrix_propagator(cnf<indexed_clause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt) :
        propagator_base(cnf, adtSolver, progParams, literalCnt), lvl(progParams.Depth) {

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
        GetGround(matrix[i], progParams.multiplicity[i] - 1);
    }
}

bool matrix_propagator::next_level_core() {
    // Try to minimize the core by brute force
    unsigned prev = UINT_MAX;
    std::vector<unsigned> core;
    std::vector<unsigned> prevCore;
    std::vector<unsigned> notFailed;
    Log("Core contains: ");
    for (unsigned c = 0; c < clauseLimitListExpr.size(); c++) {
        if (!clauseLimitListExpr[c]->is_true()) {
            if (solver->failed(clauseLimitListExpr[c]->get_lit())) {
                progParams.priority[c]++;
                core.push_back(c);
            }
            else {
                notFailed.push_back(c);
            }
        }
    }
    for (unsigned i = 0; i < core.size(); i++) {
        Log("#" << core[i]);
        if (i < core.size() - 1)
            Log(", ");
    }
    LogN("");
    for (unsigned i = core.)
    while (true) {
        core.clear();
        LogN("");

        if (core.empty() && !solver->constraint_failed())
            return true;
        if (core.size() == prev)
            break;
        prev = (unsigned)core.size();
        if (prev == 0 && solver->constraint_failed()) {
            core = std::move(prevCore);
            LogN("Fallback to previous core");
            break;
        }

        prevCore = std::move(core);

        // Let's fix the interpretation
        for (int c : notFailed) {
            solver->clause(clauseLimitListExpr[c]->get_lit());
        }

        // For the remaining we don't know; let's minimize
        for (int c : prevCore) {
            solver->constrain(clauseLimitListExpr[c]->get_lit());
        }
        solver->constrain(0);
        auto res = solver->solve();
        assert(res == 20);
    }

    unsigned maxVar = 1;
    unsigned maxValue = 0;
    for (unsigned v: core) {
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

clause_instance* matrix_propagator::get_clause_instance(const indexed_clause* clause, unsigned cpyIdx, literal selector) {
    vector<ground_literal> instances;
    instances.reserve(clause->literals.size());
    for (auto* lit : clause->literals) {
        instances.emplace_back(lit, cpyIdx);
    }
    return new clause_instance(clause, cpyIdx, selector, std::move(instances));
}

bool matrix_propagator::are_connected(const ground_literal& l1, const ground_literal& l2) {
    if (l1.Literal->polarity == l2.Literal->polarity || l1.GetArity() != l2.GetArity())
        return false;
    const auto* unification = UnificationHints.get(l1.Literal->Index, l2.Literal->Index);
    assert(unification != nullptr);
    if (large_array::is_invalid(unification))
        return false;
    bool res = unification->IsSatisfied(l1, l2);
    assert(res == UnificationHints.get(l2.Literal->Index, l1.Literal->Index)->IsSatisfied(l2, l1));
    return res;
}

void matrix_propagator::check_proof(const vector<clause_instance*>& chosen) {
    if (!progParams.CheckProof)
        return;

#if false
    unordered_map<termInstance, z3::expr> lookup;

        for (auto (v, cpy, ass, cpy2) : ADTSolver.Assignments) {
            z3::expr lhs = v.ToNewZ3(this, cpy, lookup);
            z3::expr rhs = ass.ToNewZ3(this, cpy2, lookup);
            uniSolver.add(Eq(lhs, rhs));
        }

        auto res = uniSolver.Check();
        if (res != Status.SATISFIABLE)
            throw new Exception("Could not verify consistency of connections");
        for (var clause : chosen) {
            uniSolver.Add(clause.ToNewZ3(this, lookup));
        }
        // TODO: Remove #if DEBUG
        res = uniSolver.Check();
        if (res != unsat) {
            cout << "Could not verify proof" << endl;
            exit(130);
        }
        cout << "Proof verified successful!" << endl;
#else
    throw solving_exception("Not implemented!");
#endif
}

clause_instance* matrix_propagator::GetGround(const indexed_clause* clause, unsigned cpy) {
    auto& instances = cachedClauses[clause->Index];
    for (unsigned i = instances.size(); i <= cpy; i++) {
        literal selector = m.mk_lit(new_observed_var(OPT("select#" + to_string(clause->Index) + "@" + to_string(i))));
        auto* info = get_clause_instance(clause, i, selector);
        instances.push_back(info);
        allClauses.push_back(info);
        assert(!contains_key(exprToInfo, selector));
        exprToInfo.insert(make_pair(selector, info));
    }

    return instances[cpy];
}

void matrix_propagator::assert_root() {
    assert(std::any_of(matrix.clauses.begin(), matrix.clauses.end(), [](const indexed_clause* c) { return c->Conjecture; }));
    for (unsigned i = 0; i < matrix.size(); i++) {
        if (matrix[i]->Conjecture)
            solver->add(GetGround(matrix[i], 0)->selector->get_lit());
    }
    solver->add(0);
}

vector<literal> just;
vector<literal> prop;

void matrix_propagator::pb_clause_limit() {
    if (progParams.Mode != Rectangle)
        return;

    if (chosen.size() == lvl) {
        LogN("Enforcing upper limit");
        just.clear();
        prop.clear();
        just.reserve(chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause: allClauses) {
            if (clause->value == sat)
                just.push_back(clause->selector);
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p: prop) {
            soft_propagate(just, m.mk_not(p));
        }
    }
    // both cases can apply
    if (allClauses.size() - not_chosen.size() == lvl) {
        LogN("Enforcing lower limit");
        just.clear();
        prop.clear();
        just.reserve(not_chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause: allClauses) {
            if (clause->value == unsat)
                just.push_back(m.mk_not(clause->selector));
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p: prop) {
            soft_propagate(just, p);
        }
    }
}

void matrix_propagator::fixed2(literal_term* e, bool value) {

    clause_instance* info = nullptr;
    if (!tryGetValue(exprToInfo, e, info))
        return;

    if (!value) {
        info->value = unsat;
        not_chosen.push_back(info);
        add_undo([&]() { not_chosen.back()->value = undef; not_chosen.pop_back(); });
        pb_clause_limit();
        return;
    }
    //TODO: Core pb

    unsigned c = info->clause->Index;

    /*for (unsigned i = info->copy_idx; i > 0; i--) {
        if (cachedClauses[c][i - 1]->value == sat)
            break; // If some smaller element is already assigned true, it has propagated the remaining ones already - no reason to continue
        propagate({ e }, GetGround(info->clause, i - 1)->selector);
    }*/

    if (info->copy_idx > 0) {
        auto val = cachedClauses[c][info->copy_idx - 1]->value;
        if (val != sat) {
            if (!soft_propagate({e}, GetGround(info->clause, info->copy_idx - 1)->selector))
                return;
        }
    }

    info->value = sat;
    chosen.push_back(info);
    add_undo([&]() { chosen.back()->value = undef; chosen.pop_back(); });

    if (!info->propagated) {
        // Tautology elimination
        for (int k = 0; k < info->literals.size(); k++) {
            for (int l = k + 1; l < info->literals.size(); l++) {
                if (info->literals[k].Literal->polarity != info->literals[l].Literal->polarity &&
                    info->literals[k].Literal->nameID == info->literals[l].Literal->nameID) {

                    // TODO: Store tautology constraints
                    auto* diseq = CollectConstrainUnifiable(info->literals[k], *(info->literals[l].Literal));
                    if (diseq == nullptr)
                        continue;
                    // Clause contains two complementary literals
                    // Why did the simplifier not remove those?!
                    assert(!diseq->tautology());
                    // clause->TautologyConstraints->emplace_back(k, l, diseq);

                    formula neq = diseq->GetNegConstraints(*this, info->literals[k], info->literals[l]);
                    hard_propagate({ e }, neq);
                    delete diseq;
                }
            }
        }

        if (!PropagateRules(e, info))
            return;
        info->propagated = true;
    }

    pb_clause_limit();
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
            CacheUnification(lit, cachedClause[0]->literals[j]);
            const subterm_hint* unification = UnificationHints.get(
                    lit.Literal->Index,
                    cachedClause[0]->literals[j].Literal->Index);

            if (large_array::is_invalid(unification) ||
                lit.Literal->polarity == cachedClause[0]->literals[j].Literal->polarity)
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
                CacheUnification(lit, *matrix[i]->literals[j]);
                const subterm_hint* unification = UnificationHints.get(lit.Literal->Index, matrix[i]->literals[j]->Index);
                if (large_array::is_invalid(unification) || lit.Literal->polarity == matrix[i]->literals[j]->polarity)
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

    assert(!chosen.empty());
    vector<vector<path_element>> paths;
    LogN("Final (" << ++finalCnt << ")");
    pvector<clause_instance> shuffledChosen(chosen);
    Shuffle(shuffledChosen);
    const int limit = 1;

    vector<path_element> current_path;
    FindPath(0, shuffledChosen, current_path, paths, limit);
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
                const auto* unification = UnificationHints.get(path[i].lit.Literal->Index, path[j].lit.Literal->Index);
                assert(unification != nullptr);
                if (!large_array::is_invalid(unification) && path[i].lit.Literal->polarity != path[j].lit.Literal->polarity) {
                    unification->GetPosConstraints(*this, path[i].lit, path[j].lit, unificationConstraint);
                    if (!unificationConstraint.empty())
                        constraints.push_back(m.mk_and(unificationConstraint));
                }
            }
        }

        if (progParams.Mode == Core) {
            for (auto elem: path) {
                for (unsigned i = 0; i < matrix.size(); i++) {
                    indexed_clause* cl = matrix[i];
                    unsigned literalCnt =cl ->literals.size();
                    for (int j = 0; j < literalCnt; j++) {
                        CacheUnification(elem.lit, *(cl->literals[j]));
                        const subterm_hint* unification = UnificationHints.get(
                                elem.lit.Literal->Index,
                                cl->literals[j]->Index);

                        if (large_array::is_invalid(unification) ||
                            elem.lit.Literal->polarity == cl->literals[j]->polarity)
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
                            vector<formula> cnstr = {cachedClause[maxId]->selector };
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

void matrix_propagator::FindPath(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path,
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

        path.emplace_back(*info->clause, info->copy_idx, l1);
        FindPath(clauseIdx + 1, clauses, path, foundPaths, limit);
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
