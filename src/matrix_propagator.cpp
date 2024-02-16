#include "matrix_propagator.h"

matrix_propagator::matrix_propagator(CNF<IndexedClause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt) :
        PropagatorBase(cnf, adtSolver, progParams, literalCnt), lvl(progParams.StartDepth) {

    assert(progParams.Mode == Rectangle || progParams.Mode == Core);

    multiplicity.resize(cnf.size());
    if (progParams.Mode == Core) {
        priority.resize(cnf.size());

        for (int i = 0; i < cnf.size(); i++) {
            if (cnf.IsConjecture(i))
                multiplicity[i] = 1;
        }
    }
    else {
        for (int i = 0; i < cnf.size(); i++) {
            multiplicity[i] = lvl;
        }
    }

    cachedClauses.resize(cnf.size());
    clauseLimitListExpr.resize(cnf.size());

    if (progParams.Mode == Rectangle)
        next_level_rect(lvl);
    else
        next_level_core(true);
}

void matrix_propagator::next_level_rect(unsigned inc_lvl) {
    assert(progParams.Mode == Rectangle);
    for (int i = 0; i < matrix.size(); i++) {
        if (matrix[i]->Ground) {
            GetGround(matrix[i], 0);
            multiplicity[i] = 1;
            continue;
        }
        const unsigned lim = multiplicity[i] + inc_lvl;
        for (unsigned j = multiplicity[i]; j < lim; j++) {
            GetGround(matrix[i], j - 1);
        }
        multiplicity[i] += inc_lvl;
    }
}

void matrix_propagator::next_level_core_prep() {
    core.clear();
    for (unsigned c = 0; c < matrix.size(); c++) {
        if (solver->failed((signed) c + 1)) {
            priority[c]++;
            core.push_back(c);
        }
    }

    if (core.empty()) {
        Satisfiable = true;
        return;
    }
}

void matrix_propagator::next_level_core(bool first) {
    assert(progParams.Mode == Core);

    auto instClause = [&](unsigned v) {
        assert(!matrix[v]->Ground || multiplicity[v] <= 1);

        priority[v] = 0;
        GetGround(matrix[v], cachedClauses[v].size());

//        if (!matrix[v]->Ground) {
//            clauseLimitListExpr[v] = m.mk_lit(new_observed_var("limit#" + to_string(v)));
//            clauseLimitMap.insert(make_pair(clauseLimitListExpr[v], v));
//        }
        Log("Increase clause #" + to_string(v) + " to " + to_string(cachedClauses[v].size()));
    };

    if (!first) {
        unsigned maxVar = 1;
        unsigned maxValue = 0;
        for (unsigned v: core) {
            if (priority[v] > maxValue) {
                maxVar = v;
                maxValue = priority[v];
            }
        }
        instClause(maxVar);
    }
    else {
        for (int c = 0; c < matrix.size(); c++) {
            priority[c] = 0;
            if (matrix.IsConjecture(c)) {
                GetGround(matrix[c], 0);
                multiplicity[c] = 1;
            }
            else
                multiplicity[c] = 0;

            clauseLimitListExpr[c] = m.mk_lit(new_observed_var("limit#" + to_string(c)));
            clauseLimitMap.insert(make_pair(clauseLimitListExpr[c], c));
        }
    }

    for (int i = 0; i < matrix.size(); i++) {
        if (!matrix[i]->Ground || multiplicity[i] == 0)
            solver->assume(clauseLimitListExpr[i]->get_lit());
    }
}

clause_instance* matrix_propagator::GetClauseInstanceInfo(const IndexedClause* clause, unsigned cpyIdx, literal_term* selector) {
    vector<GroundLiteral> instances;
    instances.reserve(clause->literals.size());
    for (auto* lit : clause->literals) {
        instances.emplace_back(lit, cpyIdx);
    }
    return new clause_instance(clause, cpyIdx, selector, std::move(instances));
}

bool matrix_propagator::AreConnected(const GroundLiteral& l1, const GroundLiteral& l2) {
    if (l1.Literal->polarity == l2.Literal->polarity || l1.GetArity() != l2.GetArity())
        return false;
    const auto* unification = UnificationHints.get(l1.Literal->Index, l2.Literal->Index);
    assert(unification != nullptr);
    if (Large2DArray::is_invalid(unification))
        return false;
    bool res = unification->IsSatisfied(l1, l2);
    assert(res == UnificationHints.get(l2.Literal->Index, l1.Literal->Index)->IsSatisfied(l2, l1));
    return res;
}

void matrix_propagator::CheckProof(z3::solver& uniSolver, const vector<clause_instance*>& chosen) {
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

clause_instance* matrix_propagator::GetGround(const IndexedClause* clause, unsigned int cpy) {
    auto& instances = cachedClauses[clause->Index];
    for (unsigned i = instances.size(); i <= cpy; i++) {
        literal selector = m.mk_lit(new_observed_var("select#" + to_string(clause->Index) + "@" + to_string(i)));
        auto* info = GetClauseInstanceInfo(clause, i, selector);
        instances.push_back(info);
        allClauses.push_back(info);
        assert(!contains_key(exprToInfo, selector));
        exprToInfo.insert(make_pair(selector, info));
    }

    return instances[cpy];
}

void matrix_propagator::AssertRoot() {
    for (unsigned i = 0; i < initClauses.size(); i++) {
        solver->add(GetGround(initClauses[i], 0)->selector->get_lit());
    }
    solver->add(0);
}

void matrix_propagator::pb_clause_limit() {
    if (progParams.Mode != Rectangle)
        return;

    if (chosen.size() == lvl) {
        LogN("Enforcing upper limit");
        vector<literal> just;
        vector<literal> prop;
        just.reserve(chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause: allClauses) {
            if (clause->value == sat)
                just.push_back(clause->selector);
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p: prop) {
            propagate(just, m.mk_not(p));
        }
    }
    if (allClauses.size() - not_chosen.size() == lvl) {
        LogN("Enforcing lower limit");
        vector<literal> just;
        vector<literal> prop;
        just.reserve(not_chosen.size());
        prop.reserve(allClauses.size() - (chosen.size() + not_chosen.size()));

        for (auto* clause: allClauses) {
            if (clause->value == unsat)
                just.push_back(m.mk_not(clause->selector));
            else if (clause->value == undef)
                prop.push_back(clause->selector);
        }

        for (auto* p: prop) {
            propagate(just, p);
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

    unsigned c = info->clause->Index;

    for (unsigned i = info->copy_idx; i > 0; i--) {
        if (cachedClauses[c][i - 1]->value == sat)
            break; // If some smaller element is already assigned true, it has propagated the remaining ones already - no reason to continue
        propagate({ e }, GetGround(info->clause, i - 1)->selector);
    }

#ifdef OPT
    if (progParams.Mode == Rectangle) {
            // For rect it gets better; for core worse...
            CreateTautologyConstraints(info.Clause);
            for (auto& constraint : info.Clause.TautologyConstraints) {
                GroundLiteral lit1 = info.Literals[constraint.lit1];
                GroundLiteral lit2 = info.Literals[constraint.conflicts.lit2];
                literal neq = constraint.conflicts.hint.GetNegConstraints(this, lit1, lit2);
                propagate(new[] { e }, neq);
            }
        }
#endif
    info->value = sat;
    chosen.push_back(info);
    add_undo([&]() { chosen.back()->value = undef; chosen.pop_back(); });

    if (!info->propagated) {
        PropagateRules(e, info);
        info->propagated = true;
    }

    pb_clause_limit();
}

formula_term* matrix_propagator::ConnectLiteral(clause_instance* info, const GroundLiteral& lit) {
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
            const SubtermHint* unification = UnificationHints.get(
                    lit.Literal->Index,
                    cachedClause[0]->literals[j].Literal->Index);

            if (Large2DArray::is_invalid(unification) ||
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
                const SubtermHint* unification = UnificationHints.get(lit.Literal->Index, matrix[i]->literals[j]->Index);
                if (Large2DArray::is_invalid(unification) || lit.Literal->polarity == matrix[i]->literals[j]->polarity)
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
                                   })
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
    if (progParams.Mode == Core) {
        // TODO:
        throw solving_exception("TODO");
        for (auto& p : chosen) {
            if (p->copy_idx == multiplicity[p->clause->Index] - 1 && !p->clause->Ground) {
                justifications.push_back(clauseLimitListExpr[p->clause->Index]);
            }
        }
    }
    for (auto& path : paths) {
        vector<formula> constraints;
        for (int i = 0; i < path.size(); i++) {
            for (int j = i + 1; j < path.size(); j++) {
                assert(!AreConnected(path[i].lit, path[j].lit));
                vector<formula> unificationConstraint;
                const auto* unification = UnificationHints.get(path[i].lit.Literal->Index, path[j].lit.Literal->Index);
                assert(unification != nullptr);
                if (!Large2DArray::is_invalid(unification) && path[i].lit.Literal->polarity != path[j].lit.Literal->polarity) {
                    unification->GetPosConstraints(*this, path[i].lit, path[j].lit, unificationConstraint);
                    if (!unificationConstraint.empty())
                        constraints.push_back(m.mk_and(unificationConstraint));
                }
            }
        }
        if (constraints.empty()) {
            propagate_conflict(justifications);
            return;
        }
        propagate(justifications, m.mk_or(constraints));
    }
}

void matrix_propagator::FindPath(int clauseIdx, const vector<clause_instance*>& clauses, vector<path_element>& path,
                                 vector<vector<path_element>>& foundPaths, int limit) {
    if (clauseIdx >= clauses.size()) {
        foundPaths.push_back(path);
#ifndef NDEBUG
        for (int i = 0; i < path.size(); i++) {
            for (int j = i + 1; j < path.size(); j++) {
                assert(!AreConnected(path[i].lit, path[j].lit));
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
            if (AreConnected(l1, elem.lit)) {
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

void matrix_propagator::reinit_solver2() {
    for (auto* clause : allClauses) {
        clause->propagated = false;
    }
}
