#include "matrix_propagator.h"

static unsigned conflicts = 0;
static unsigned cnt = 0;

complex_adt_solver::~complex_adt_solver() {
    for (auto& solver : solvers) {
        delete solver;
    }
}

void complex_adt_solver::reset(matrix_propagator* propagator) {
    prop = propagator;
    exprToEq.clear();
    exprToLess.clear();
    eqToExpr.clear();
    lessToExpr.clear();

    for (const auto* s : solvers) {
        for (auto term : s->hashCon) {
            term.second->reset();
        }
    }
}

simple_adt_solver* complex_adt_solver::new_solver(const string& name) {
    auto* adtSolver = new simple_adt_solver(*this, solvers.size());
    nameToSolver.insert(make_pair(name, adtSolver));
    solvers.push_back(adtSolver);
    SortNames.push_back(name);
    return adtSolver;
}

simple_adt_solver* complex_adt_solver::get_solver(const string& name) {
    simple_adt_solver* solver = nullptr;
    return tryGetValue(nameToSolver, name, solver) ? solver : new_solver(name);
}

bool complex_adt_solver::asserted(literal e, bool isTrue) {
    equality info;
    if (!tryGetValue(exprToEq, e, info))
        return false;
    //if (++cnt % 1000 == 0) {
    //    cout << conflicts << " non-unify conflicts" << endl;
    //}
    assert(info.just.litJust.size() == 1 && info.just.eqJust.empty() && info.just.litJust[0] == e);

    auto* lhsInfo = info.LHS->origin;
    auto* rhsInfo = info.RHS->origin;
    assert(!(info.LHS->t->is_ground() && info.RHS->t->is_ground()));
    assert(!(lhsInfo == nullptr && rhsInfo == nullptr));

    if (lhsInfo != nullptr && lhsInfo->value == unsat) {
        LogN("Dropped");
        return false;
    }
    if (rhsInfo != nullptr && rhsInfo->value == unsat) {
        LogN("Dropped");
        return false;
    }
    if (lhsInfo != nullptr && lhsInfo->value == undef) {
        LogN("Shelved");
        if (isTrue) {
            lhsInfo->delayedRelevantTrue.push_back(std::move(info));
            propagator().add_undo([lhsInfo]() { lhsInfo->delayedRelevantTrue.pop_back(); });
        }
        else {
            lhsInfo->delayedRelevantFalse.push_back(std::move(info));
            propagator().add_undo([lhsInfo]() { lhsInfo->delayedRelevantFalse.pop_back(); });
        }
        return true;
    }
    if (rhsInfo != nullptr && rhsInfo->value == undef) {
        LogN("Shelved");
        if (isTrue) {
            rhsInfo->delayedRelevantTrue.push_back(std::move(info));
            propagator().add_undo([rhsInfo]() { rhsInfo->delayedRelevantTrue.pop_back(); });
        }
        else {
            rhsInfo->delayedRelevantFalse.push_back(std::move(info));
            propagator().add_undo([rhsInfo]() { rhsInfo->delayedRelevantFalse.pop_back(); });
        }
        return true;
    }
    LogN("Processed");

    try {
        asserted(e, info.LHS, info.RHS, isTrue);
    }
    catch (...) {
        cout << "Crashed unify" << endl;
        exit(132);
    }
    return true;
}

bool complex_adt_solver::asserted(literal e, term_instance* lhs, term_instance* rhs, bool isTrue) const {
    assert(&lhs->t->Solver == &rhs->t->Solver);
    if (propagator().is_adt_split()) {
        return isTrue
               ? //lhs->t->Solver.unify_split(e, lhs, rhs)
               lhs->t->Solver.unify(e, lhs, rhs)
               : lhs->t->Solver.non_unify_split(prop->m.mk_not(e), lhs, rhs);
    }
    return isTrue
           ? lhs->t->Solver.unify(e, lhs, rhs)
           : lhs->t->Solver.non_unify(prop->m.mk_not(e), lhs, rhs);
}

bool complex_adt_solver::preprocess_equality(term_instance* lhs, term_instance* rhs, vector<equality>& subproblems) {
    stack<pair<term_instance*, term_instance*>> stack;
    stack.emplace(lhs, rhs);

    while (!stack.empty()) {
        auto [lhs2, rhs2] = stack.top();
        stack.pop();
        if (lhs2->t->id() == rhs2->t->id() && (lhs2->cpy_idx() == rhs2->cpy_idx() || lhs2->t->is_ground()))
            continue;
        if (lhs2->t->is_const() && rhs2->t->is_const()) {
            if (lhs2->t->FuncID != rhs2->t->FuncID)
                return false;
            for (unsigned i = 0; i < lhs2->t->Args.size(); i++) {
                stack.emplace(lhs2->t->Args[i]->get_instance(lhs2->cpy_idx(), propagator()),
                              rhs2->t->Args[i]->get_instance(rhs2->cpy_idx(), propagator()));
            }
        }
        else {
            subproblems.emplace_back(lhs2, rhs2);
        }
    }
    return true;
}

bool
complex_adt_solver::preprocess_less(term_instance* lhs, term_instance* rhs, bool eq, vector<less_than>& subproblems) {
    stack<less_than> stack;
    vector<less_than> comparisons;
    stack.emplace(lhs, rhs);

    while (!stack.empty()) {
        auto [lhs2, rhs2] = stack.top();
        stack.pop();
        if (lhs2 == rhs2) {
            if (eq)
                continue;
            return false;
        }

        if (lhs2->t->is_const() && rhs2->t->is_const()) {
            if (lhs2->t->FuncID != rhs2->t->FuncID)
                return lhs2->t->FuncID < rhs2->t->FuncID;
        }

        assert((lhs->t->is_var() || rhs->t->is_var()) && lhs != rhs);

        if (lhs2->t->id() == rhs2->t->id() && (lhs2->cpy_idx() == rhs2->cpy_idx() || lhs2->t->is_ground()))
            continue;
        if (lhs2->t->is_const() && rhs2->t->is_const()) {
            if (lhs2->t->FuncID != rhs2->t->FuncID)
                return false;
            for (unsigned i = 0; i < lhs2->t->Args.size(); i++) {
                stack.emplace(lhs2->t->Args[i]->get_instance(lhs2->cpy_idx(), propagator()),
                              rhs2->t->Args[i]->get_instance(rhs2->cpy_idx(), propagator()));
            }
        }
        else {
            subproblems.emplace_back(lhs2, rhs2);
        }
    }
    return true;

    unsigned prevGreaterCnt = r1->greater.size();
    unsigned prevSmallerCnt = r2->smaller.size();

    justification just1;
    just1.add_literal(just);
    justification just2;
    just2.add_literal(just);

    r1->greater.emplace_back(r2, eq, just1);
    r2->smaller.emplace_back(r1, eq, just2);

    propagator().add_undo([r1, r2, prevGreaterCnt, prevSmallerCnt]() {
        r1->greater.pop_back();
        r2->smaller.pop_back();
        assert(r1->greater.size() == prevGreaterCnt);
        assert(r2->smaller.size() == prevSmallerCnt);
    });

    justification j;
    j.add_literal(just);
    vector<term_instance*> path;
    if (!check(r1, r2, eq, j, path, false))
        return false;
    assert(path.empty());
    assert(j.litJust.size() == 1 && j.eqJust.empty());
    if (!check(r2, r1, eq, j, path, true))
        return false;

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            if (r1->t->FuncID < r2->t->FuncID)
                return true;
            assert(r1->t->FuncID > r2->t->FuncID);
            justification justList;
            justList.add_literal(just);
            justList.add_equality(lhs, r1);
            justList.add_equality(rhs, r2);
            conflict(justList);
            return false;
        }

        assert(!r1->t->Args.empty());

        vector<formula> cases;
        cases.reserve(r1->t->Args.size() + (eq ? 1 : 0));

        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            vector<formula> cases2;
            cases2.reserve(i + 1);
            for (unsigned j = 0; j < i; j++) {
                cases2[j] = complexSolver.make_equality_expr(
                        r1->t->Args[j]->get_instance(r1->cpy_idx(), propagator()),
                        r2->t->Args[j]->get_instance(r2->cpy_idx(), propagator()));
            }
            cases2[i] = complexSolver.make_less_expr(
                    r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                    r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator()));
            cases[i] = propagator().m.mk_and(cases2);
        }
        if (eq) {
            vector<formula> cases2;
            cases2.reserve(r1->t->Args.size());
            for (int i = 0; i < r1->t->Args.size(); i++) {
                cases2[i] = complexSolver.make_equality_expr(
                        r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                        r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator()));
            }
            cases[r1->t->Args.size()] = propagator().m.mk_and(cases2);
        }
        justification justList;
        justList.add_literal(just);
        justList.add_equality(lhs, r1);
        justList.add_equality(rhs, r2);
        propagate(justList, propagator().m.mk_or(cases));
        return true;
    }
    if (r1->t->is_var()) {
        r1->smaller_watches.emplace_back(lhs, rhs, eq, just);
        propagator().add_undo([r1]() { r1->smaller_watches.pop_back(); });
    }
    else {
        r2->smaller_watches.emplace_back(lhs, rhs, eq, just);
        propagator().add_undo([r2]() { r2->smaller_watches.pop_back(); });
    }

    return true;
}

formula complex_adt_solver::make_equality_expr(term_instance* lhs, term_instance* rhs) {

    equality eq(lhs, rhs);
    formula expr = nullptr;
    if (tryGetValue(eqToExpr, eq, expr))
        return expr;

    vector<equality> subproblems;
    if (!preprocess_equality(lhs, rhs, subproblems)) {
        expr = prop->m.mk_false();
        eqToExpr.insert(make_pair(eq, expr));
        return expr;
    }

    vector<formula> cases;
    vector<literal> cases2;
    cases.reserve(subproblems.size());

    for (auto eq2 : subproblems) {
        if (!tryGetValue(eqToExpr, eq2, expr)) {
            expr = prop->m.mk_lit(prop->new_observed_var(OPT(eq2.to_string())));
            eq2.just.add_literal((literal)expr);
            exprToEq.insert(make_pair((literal)expr, eq2));
            eqToExpr.insert(make_pair(eq2, expr));
        }
        cases.push_back(expr);
        cases2.push_back((literal)expr);
    }

    if (subproblems.size() == 1 && subproblems[0] == eq)
        return cases[0]; // There was absolutely no change -> the loop before created the atom already

    expr = prop->m.mk_and(cases);
    eq.just.add_literals(cases2);
    eqToExpr.insert(make_pair(eq, expr));
    return expr;
}

formula complex_adt_solver::make_disequality_expr(term_instance* lhs, term_instance* Rhs) {
    return prop->m.mk_not(make_equality_expr(lhs, Rhs));
}

literal complex_adt_solver::make_less_expr(term_instance* lhs, term_instance* rhs) {
    if (lhs->t->id() == rhs->t->id() && (lhs->cpy_idx() == rhs->cpy_idx() || lhs->t->is_ground()))
        return prop->m.mk_false();
    if (lhs->t->is_const() == rhs->t->is_const()) {
        // TODO: Proper preprocessing
        if (lhs->t->FuncID < rhs->t->FuncID)
            return prop->m.mk_true();
        if (lhs->t->FuncID > rhs->t->FuncID)
            return prop->m.mk_false();
    }

    less_than le(lhs, rhs);

    literal expr = nullptr;
    if (tryGetValue(lessToExpr, le, expr))
        return expr;
    expr = prop->m.mk_lit(prop->new_observed_var(OPT(le.to_string())));
    exprToLess.insert(make_pair(expr, le));
    lessToExpr.insert(make_pair(le, expr));
    return expr;
}

literal complex_adt_solver::make_greater_eq_expr(term_instance* lhs, term_instance* rhs) {
    return prop->m.mk_not(make_less_expr(lhs, rhs));
}

void complex_adt_solver::peek_term(const string& solver, const string& name, int argCnt) {
    get_solver(solver)->peek_term(name, argCnt);
}

void simple_adt_solver::conflict(const justification& just) {
    if (propagator().is_conflict())
        return;
    vector<literal> justExpr;
    just.resolve_justification(this, justExpr);
    propagator().propagate_conflict(justExpr);
}

void simple_adt_solver::propagate(const justification& just, formula prop) {
    if (propagator().is_conflict())
        return;
    vector<literal> justExpr;
    just.resolve_justification(this, justExpr);
    propagator().hard_propagate(justExpr, prop);
}

bool simple_adt_solver::soft_propagate(const justification& just, literal prop) {
    if (propagator().is_conflict())
        return false;
    vector<literal> justExpr;
    just.resolve_justification(this, justExpr);
    return propagator().soft_propagate(justExpr, prop);
}

void simple_adt_solver::ensure_founded() {
    // Only required for Z3 expressions
    if (any_of(domains.cbegin(), domains.cend(), [](const std::vector<unsigned>& o) { return o.empty(); }))
        return;
    string name = "a_" + complexSolver.get_solver_name(id());
    int idx = 1;
    if (contains_key(nameToId, name)) {
        peek_term(name, 0);
        return;
    }
    while (contains_key(nameToId, name + std::to_string(idx++))) {}
    peek_term(name, 0);
}

bool complex_adt_solver::are_equal(term_instance* lhs, term_instance* rhs) {
    return lhs->t->Solver.solverId == rhs->t->Solver.solverId && lhs->t->Solver.are_equal(lhs, rhs);
}

void complex_adt_solver::make_z3_adt(z3::context& ctx) {
    vector<vector<Z3_constructor>> constructors;
    constructors.reserve(SortNames.size());
    vector<Z3_symbol> constructor_names;
    constructor_names.reserve(SortNames.size());

    for (unsigned i = 0; i < solvers.size(); i++) {
        auto& solver = *solvers[i];
        constructor_names.push_back(Z3_mk_string_symbol(ctx, get_solver_name(i).c_str()));
        solver.ensure_founded();
        constructors.emplace_back();
        constructors.back().reserve(solver.funcNames.size());
        for (int j = 0; j < solver.funcNames.size(); j++) {
            string funcName = solver.funcNames[j];
            vector<unsigned>& domain = solver.domains[j];
            unsigned arity = domain.size();

            vector<Z3_symbol> fields;
            fields.reserve(arity);
            for (unsigned k = 0; k < arity; k++) {
                fields.push_back(ctx.str_symbol((funcName + "_arg" + std::to_string(k)).c_str()));
            }

            Z3_symbol name = Z3_mk_string_symbol(ctx, funcName.c_str());
            Z3_symbol recognizer = Z3_mk_string_symbol(ctx, ("is_" + funcName).c_str());
            z3::sort s(ctx);
            vector<Z3_sort> sorts;
            sorts.reserve(arity);
            for (unsigned k = 0; k < arity; k++) {
                sorts.push_back(s);
            }
            auto* c = Z3_mk_constructor(ctx, name, recognizer,
                                        arity, fields.data(),
                                        sorts.data(), domain.data());

            constructors[i].push_back(c);
            nameToSolver.insert(make_pair(funcName, &solver));
        }
    }

    unsigned n = constructor_names.size();
    vector<Z3_constructor_list> constructorList;
    constructorList.reserve(n);
    vector<Z3_sort> n_res;
    n_res.resize(n);
    for (unsigned i = 0; i < n; i++) {
        constructorList.push_back(Z3_mk_constructor_list(ctx, constructors[i].size(), constructors[i].data()));
    }

    Z3_mk_datatypes(ctx, n, constructor_names.data(), n_res.data(), constructorList.data());
    for (unsigned i = 0; i < n; i++) {
        solvers[i]->z3Sort = z3::sort(ctx, n_res[i]);
    }

    for (auto& list : constructors) {
        for (auto* c : list) {
            Z3_del_constructor(ctx, c);
        }
    }
    for (auto& list : constructorList) {
        Z3_del_constructor_list(ctx, list);
    }
}

simple_adt_solver::~simple_adt_solver() {
    for (auto& list : hashCon) {
        delete list.second;
    }
    if (z3Sort.has_value())
        z3Sort.reset();
}

string simple_adt_solver::pretty_print(const term* t, unsigned cpyIdx,
                                       unordered_map<term_instance*, string>* prettyNames) const {
    if (t->FuncID < 0) {
        if (prettyNames == nullptr)
            return "var " + varNames[-t->FuncID - 1];
        string name;
        if (tryGetValue(*prettyNames, t->get_instance(cpyIdx, propagator()), name))
            return name;
        prettyNames->insert(
                make_pair(t->get_instance(cpyIdx, propagator()), name = "$" + std::to_string(prettyNames->size())));
        return name;
    }

    if (t->Args.empty())
        return funcNames[t->FuncID];
    std::stringstream sb;
    sb << funcNames[t->FuncID];
    sb << '(' << pretty_print(t->Args[0], cpyIdx, prettyNames);
    for (int i = 1; i < t->Args.size(); i++) {
        sb << ',' << pretty_print(t->Args[i], cpyIdx, prettyNames);
    }
    sb << ')';
    return sb.str();
}

int simple_adt_solver::peek_term(const string& name, unsigned argCnt) {
    std::vector<unsigned> domain(argCnt, solverId);
    return peek_term(name, std::move(domain));
}

int simple_adt_solver::peek_term(const string& name, vector<unsigned> domain) {
    int id = 0;
    if (!tryGetValue(nameToId, name, id)) {
        id = (int)funcNames.size();
        domains.push_back(std::move(domain));
        funcNames.push_back(name);
        nameToId.insert(make_pair(name, id));
    }
    if (id < 0)
        throw solving_exception("Name already used by variable");
    return id;
}

term* simple_adt_solver::make_term(int id, const vector<term*>& args, const indexed_clause* clause) {
    assert(id >= 0);
    if (id >= funcNames.size())
        throw solving_exception("Term index out of bounds");
    return make_term_internal(id, args, clause);
}

term* simple_adt_solver::make_term_internal(int id, const vector<term*>& args, const indexed_clause* clause) {
    const RawTermWrapper key(new raw_term(id, args));
    term* t = nullptr;
    if (tryGetValue(hashCon, key, t)) {
        delete key.obj;
        return t;
    }
    delete key.obj;
    t = new term(id, args, *this, hashCon.size(), clause);
    hashCon.insert(make_pair(RawTermWrapper(t), t));
    return t;
}

term* simple_adt_solver::make_var(const string& name, const indexed_clause* clause) {
    int id = 0;
    if (!tryGetValue(nameToId, name, id)) {
        id = -((int)varNames.size() + 1);
        varNames.push_back(name);
        nameToId.insert(make_pair(name, id));
    }
    if (id >= 0)
        throw solving_exception("Name already used by function");
    return make_var(-id - 1, clause);
}

term* simple_adt_solver::make_var(int idx, const indexed_clause* clause) {
    if (idx >= varNames.size())
        throw solving_exception("Variable index out of bounds");
    return make_term_internal(-(idx + 1), {}, clause);
}

bool simple_adt_solver::update_diseq(term_instance* b, term_instance* newRoot) {
    assert(b->find_root(propagator()) == newRoot);
    for (auto& info : newRoot->diseq_watches) {
        if (non_unify(info) == z3::check_result::unsat)
            // TODO: Swap remove if sat
            return false;
    }

    unsigned prevSize = newRoot->diseq_watches.size();
    propagator().add_undo([newRoot, prevSize]() {
        newRoot->diseq_watches.resize(prevSize);
    });

    for (auto& info : b->diseq_watches) {
        switch (non_unify(info)) {
            case z3::check_result::unsat:
                return false;
            case z3::check_result::unknown:
                newRoot->diseq_watches.push_back(info);
                break;
        }
    }
    return true;
}

bool simple_adt_solver::update_ineq(term_instance* newRoot) {
    assert(newRoot->is_root());
    unsigned cnt = newRoot->greater.size();
    for (auto i = 0; i < cnt; i++) {
        auto& [inst, eq, just] = newRoot->greater[i];
        justification j(just);
        vector<term_instance*> path;
        if (!check(newRoot, inst, eq, j, path, false))
            return false;
    }
    cnt = newRoot->smaller.size();
    for (unsigned i = 0; i < cnt; i++) {
        auto& [inst, eq, just] = newRoot->smaller[i];
        justification j(just);
        vector<term_instance*> path;
        if (!check(newRoot, inst, eq, j, path, true))
            return false;
    }
    return true;
}

string simple_adt_solver::to_string() const {
    stringstream sb;
    for (int i = 0; i < funcNames.size(); i++) {
        sb << funcNames[i] << '/' << std::to_string(domains[i].size());
    }
    return sb.str();
}

bool simple_adt_solver::unify_split(literal just, term_instance* lhs, term_instance* rhs) {
    justification justList;
    justList.add_literal(just);
    return unify_split(lhs, rhs, justList);
}

bool simple_adt_solver::unify_split(term_instance* lhs, term_instance* rhs, justification& justList) {
    assert(lhs != rhs);
    assert(!lhs->t->is_const() || !rhs->t->is_const()); // Why would the simplifier fail?
    auto* r1 = lhs->find_root(propagator());
    auto* r2 = rhs->find_root(propagator());

    if (r1 == r2)
        return true;

    justList.add_equality(r1, lhs);
    justList.add_equality(r2, rhs);

    if (!merge_root(r1, r2, { lhs, rhs, justList })) {
        conflict(justList);
        return false;
    }

    if (lhs == r1 && rhs == r2) {
        /*if (!lhs->t->is_const()) {
            lhs->eq_split_watches.emplace_back(lhs, rhs, justList);
            propagator().add_undo([lhs]() {
                lhs->eq_split_watches.pop_back();
            });
        }
        if (!rhs->t->is_const()) {
            rhs->eq_split_watches.emplace_back(lhs, rhs, justList);
            propagator().add_undo([rhs]() {
                rhs->eq_split_watches.pop_back();
            });
        }*/
        return true;
    }

    formula f = complexSolver.make_equality_expr(r1, r2);
    assert(!f->is_true());
    if (f->is_false()) {
        conflict(justList);
        return false;
    }

    if (f->is_literal())
        return soft_propagate(justList, (literal)f);
    for (const auto& arg : ((and_term*)f)->get_args()) {
        assert(arg->is_literal() && !arg->is_true() && !arg->is_false());
        soft_propagate(justList, (literal)arg);
    }
    return true;
}

bool simple_adt_solver::non_unify_split(literal just, term_instance* lhs, term_instance* rhs) {
    justification justList;
    justList.add_literal(just);
    return non_unify_split(lhs, rhs, justList);
}

bool simple_adt_solver::non_unify_split(term_instance* lhs, term_instance* rhs, justification& justList) {
    assert(!lhs->t->is_const() || !rhs->t->is_const()); // Why would the simplifier fail?
    auto* r1 = lhs->find_root(propagator());
    auto* r2 = rhs->find_root(propagator());


    justList.add_equality(r1, lhs);
    justList.add_equality(r2, rhs);

    if (r1 == r2) {
        conflict(justList);
        return true;
    }

    if (lhs == r1 && rhs == r2) {
        if (!lhs->t->is_const()) {
            lhs->diseq_split_watches.emplace_back(lhs, rhs, std::move(justList));
            propagator().add_undo([lhs]() {
                lhs->diseq_split_watches.pop_back();
            });
            return true;
        }
        assert(!rhs->t->is_const());
        rhs->diseq_split_watches.emplace_back(lhs, rhs, std::move(justList));
        propagator().add_undo([rhs]() {
            rhs->diseq_split_watches.pop_back();
        });
        return true;
    }

    if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID)
        return true;

    formula f = complexSolver.make_disequality_expr(r1, r2);
    assert(!f->is_true());
    if (f->is_false()) {
        conflict(justList);
        return false;
    }

    if (f->is_literal())
        return soft_propagate(justList, (literal)f);
    propagate(justList, f);
    return true;
}

bool simple_adt_solver::unify(literal just, term_instance* lhs, term_instance* rhs) {
    justification justList;
    justList.add_literal(just);
    return unify(lhs, rhs, justList);
}

bool simple_adt_solver::are_equal(term_instance* lhs, term_instance* rhs) {
    if (lhs->t->id() == rhs->t->id() && (lhs->cpy_idx() == rhs->cpy_idx() || lhs->t->is_ground()))
        return true;
    if (lhs->t->is_ground() && rhs->t->is_ground() && lhs->t->id() != rhs->t->id())
        return false;
    term_instance* r1 = lhs->find_root(propagator());
    term_instance* r2 = rhs->find_root(propagator());
    if (r1 == r2)
        return true;
    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID)
            return false;
        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            if (!are_equal(r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                           r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator())))
                return false;
        }
        return true;
    }
    return false;
}

bool simple_adt_solver::unify(term_instance* lhs, term_instance* rhs, justification& justifications) {

    if (lhs->t->id() == rhs->t->id() && (lhs->cpy_idx() == rhs->cpy_idx() || lhs->t->is_ground()))
        return true;
    if (lhs->t->is_ground() && rhs->t->is_ground() && lhs->t->id() != rhs->t->id()) {
        conflict(justifications);
        return false;
    }

    term_instance* r1 = lhs->find_root(propagator());
    term_instance* r2 = rhs->find_root(propagator());
    justifications.add_equality(lhs, r1);
    justifications.add_equality(rhs, r2);

    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            conflict(justifications);
            return false;
        }
        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            if (!unify(r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                       r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator()), justifications))
                return false;
        }
        justifications.remove_equality();
        justifications.remove_equality();
        return true;
    }

    if (merge_root(r1, r2, { lhs, rhs, { justifications }})) {
        justifications.remove_equality();
        justifications.remove_equality();
        return true;
    }
    conflict(justifications);
    return false;
}

z3::check_result simple_adt_solver::non_unify(Lazy* lazy) {
    if (lazy->Solved)
        return z3::check_result::sat;

    unsigned prevLitSize = lazy->just.litJust.size();
    unsigned prevEqSize = lazy->just.eqJust.size();
    auto* prevLHS = lazy->LHS;
    auto* prevRHS = lazy->RHS;
    auto prevPrev = lazy->prev;

    propagator().add_undo([lazy, prevLitSize, prevEqSize, prevLHS, prevRHS, prevPrev]() {
        lazy->just.litJust.resize(prevLitSize);
        lazy->just.eqJust.resize(prevEqSize);
        lazy->LHS = prevLHS;
        lazy->RHS = prevRHS;
        lazy->Solved = false;
        lazy->prev = prevPrev;
    });

    while (lazy->LHS != nullptr || !lazy->prev.empty()) {
        if (lazy->LHS == nullptr) {
            // don't worry about undoing operations on lazy; we copy it anyway
            assert(lazy->RHS == nullptr);
            auto current = lazy->prev.top();
            if (current.argIdx >= current.lhs->t->Args.size()) {
                lazy->prev.pop();
                continue;
            }
            lazy->LHS = current.lhs->t->Args[current.argIdx]->get_instance(current.lhs->cpy_idx(), propagator());
            lazy->RHS = current.rhs->t->Args[current.argIdx]->get_instance(current.rhs->cpy_idx(), propagator());
            current.argIdx++;
        }

        assert(lazy->LHS != nullptr);
        assert(lazy->RHS != nullptr);

        term_instance* r1 = lazy->LHS->find_root(propagator());
        term_instance* r2 = lazy->RHS->find_root(propagator());
        if (r1 == r2) {
            lazy->just.add_equality(lazy->LHS, lazy->RHS);
            lazy->LHS = nullptr;
            lazy->RHS = nullptr;
            continue;
        }
        if (r1->t->is_ground() && r2->t->is_ground() && r1->t->id() != r2->t->id()) {
            lazy->Solved = true;
            return z3::check_result::sat;
        }
        if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID) {
            lazy->Solved = true;
            return z3::check_result::sat;
        }

        if (r1->t->is_var() || r2->t->is_var()) {
            assert((lazy->LHS != nullptr && lazy->RHS != nullptr) || !lazy->prev.empty());
            return z3::check_result::unknown;
        }

        assert(r1->t->Args.size() == r2->t->Args.size());

        lazy->just.add_equality(lazy->LHS, r1);
        lazy->just.add_equality(lazy->RHS, r2);

        if (r1->t->Args.size() == 1) {
            lazy->LHS = r1->t->Args[0]->get_instance(r1->cpy_idx(), propagator());
            lazy->RHS = r2->t->Args[0]->get_instance(r2->cpy_idx(), propagator());
            continue;
        }

        lazy->LHS = nullptr;
        lazy->RHS = nullptr;

        lazy->prev.emplace(r1, r2);
    }

    conflicts++;
    conflict(lazy->just);
    return z3::check_result::unsat;
}

bool simple_adt_solver::check_cycle(term_instance* inst, justification& justifications) {
    if (!inst->t->is_const() || inst->t->is_ground())
        return true;
    auto* r = inst->find_root(propagator());
    justifications.add_equality(inst, r);
    for (auto* arg : inst->t->Args) {
        if (!check_cycle(arg->get_instance(inst->cpy_idx(), propagator()), r, justifications))
            return false;
    }
    justifications.remove_equality();
    return true;
}

bool simple_adt_solver::check_cycle(term_instance* inst, term_instance* search, justification& justifications) {
    assert(search->is_root());
    auto* r = inst->find_root(propagator());

    if (r == search) {
        // Found the cycle
        justifications.add_equality(inst, r);
        conflict(justifications);
        return false;
    }

    if (r->t->is_var())
        return true;

    justifications.add_equality(inst, r);
    for (auto* arg : r->t->Args) {
        if (!check_cycle(arg->get_instance(r->cpy_idx(), propagator()), search, justifications))
            return false;
    }
    justifications.remove_equality();
    return true;
}

bool simple_adt_solver::non_unify(literal just, term_instance* lhs, term_instance* rhs) {
    // return true;
    // TODO: Why is it faster without this?!
    Lazy* lazy = new Lazy(lhs, rhs);
    lazy->just.add_literal(just);
    propagator().add_undo([lazy]() { delete lazy; });
    z3::check_result status = non_unify(lazy);
    if (status == z3::check_result::sat || lazy->Solved)
        return true;
    if (status == z3::check_result::unsat)
        return false;

    assert(lazy->LHS != nullptr);

    auto* r = lazy->LHS->find_root(propagator());
    if (r->t->is_var()) {
        propagator().add_undo([r]() { r->diseq_watches.pop_back(); });
        r->diseq_watches.push_back(lazy);
        return true;
    }
    r = lazy->RHS->find_root(propagator());
    assert(r->t->is_var());
    propagator().add_undo([r]() { r->diseq_watches.pop_back(); });
    r->diseq_watches.push_back(lazy);
    return true;
}

bool simple_adt_solver::less(literal just, term_instance* lhs, term_instance* rhs, bool eq) {

    auto* r1 = lhs->find_root(propagator());
    auto* r2 = rhs->find_root(propagator());

    if (r1 == r2) {
        if (eq)
            return true;
        justification j;
        j.add_literal(just);
        j.add_equality(lhs, rhs);
        conflict(j);
        return false;
    }

    unsigned prevGreaterCnt = r1->greater.size();
    unsigned prevSmallerCnt = r2->smaller.size();

    justification just1;
    just1.add_literal(just);
    justification just2;
    just2.add_literal(just);

    r1->greater.emplace_back(r2, eq, just1);
    r2->smaller.emplace_back(r1, eq, just2);

    propagator().add_undo([r1, r2, prevGreaterCnt, prevSmallerCnt]() {
        r1->greater.pop_back();
        r2->smaller.pop_back();
        assert(r1->greater.size() == prevGreaterCnt);
        assert(r2->smaller.size() == prevSmallerCnt);
    });

    justification j;
    j.add_literal(just);
    vector<term_instance*> path;
    if (!check(r1, r2, eq, j, path, false))
        return false;
    assert(path.empty());
    assert(j.litJust.size() == 1 && j.eqJust.empty());
    if (!check(r2, r1, eq, j, path, true))
        return false;

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            if (r1->t->FuncID < r2->t->FuncID)
                return true;
            assert(r1->t->FuncID > r2->t->FuncID);
            justification justList;
            justList.add_literal(just);
            justList.add_equality(lhs, r1);
            justList.add_equality(rhs, r2);
            conflict(justList);
            return false;
        }

        assert(!r1->t->Args.empty());

        vector<formula> cases;
        cases.reserve(r1->t->Args.size() + (eq ? 1 : 0));

        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            vector<formula> cases2;
            cases2.reserve(i + 1);
            for (unsigned j = 0; j < i; j++) {
                cases2[j] = complexSolver.make_equality_expr(
                        r1->t->Args[j]->get_instance(r1->cpy_idx(), propagator()),
                        r2->t->Args[j]->get_instance(r2->cpy_idx(), propagator()));
            }
            cases2[i] = complexSolver.make_less_expr(
                    r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                    r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator()));
            cases[i] = propagator().m.mk_and(cases2);
        }
        if (eq) {
            vector<formula> cases2;
            cases2.reserve(r1->t->Args.size());
            for (int i = 0; i < r1->t->Args.size(); i++) {
                cases2[i] = complexSolver.make_equality_expr(
                        r1->t->Args[i]->get_instance(r1->cpy_idx(), propagator()),
                        r2->t->Args[i]->get_instance(r2->cpy_idx(), propagator()));
            }
            cases[r1->t->Args.size()] = propagator().m.mk_and(cases2);
        }
        justification justList;
        justList.add_literal(just);
        justList.add_equality(lhs, r1);
        justList.add_equality(rhs, r2);
        propagate(justList, propagator().m.mk_or(cases));
        return true;
    }
    if (r1->t->is_var()) {
        r1->smaller_watches.emplace_back(lhs, rhs, eq, just);
        propagator().add_undo([r1]() { r1->smaller_watches.pop_back(); });
    }
    else {
        r2->smaller_watches.emplace_back(lhs, rhs, eq, just);
        propagator().add_undo([r2]() { r2->smaller_watches.pop_back(); });
    }

    return true;
}

bool simple_adt_solver::check(term_instance* start, term_instance* current, bool eq, justification& just,
                              vector<term_instance*>& path, bool smaller) {
    term_instance* r1 = start->find_root(propagator());
    term_instance* r2 = current->find_root(propagator());
    if (r1 == r2) {
        if (eq) {
            for (auto* p : path) {
                equality equality(start, p, { just });
                merge_root(start, p, equality, false);
            }
            return true;
        }
        conflict(just);
        return false;
    }
    just.add_equality(start, r1);
    just.add_equality(current, r2);
    if (start->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID &&
        smaller == (r1->t->FuncID < r2->t->FuncID)) {
        conflict(just);
        return false;
    }
    if (eq)
        path.push_back(current);

    unsigned cnt = smaller ? r2->smaller.size() : r2->greater.size();
    for (auto i = 0; i < cnt; i++) {
        auto& [inst, b, justifications] = (smaller ? r2->smaller : r2->greater)[i];

        if (inst->find_root(propagator()) == r2) {
            assert(b);
            continue;
        }

        unsigned prevLit = just.litJust.size();
        unsigned prevEq = just.eqJust.size();
        just.add(justifications);
        if (!check(r1, inst, eq && b, just, path, smaller))
            return false;
        just.litJust.resize(prevLit);
        just.eqJust.resize(prevEq);
    }

    if (eq)
        path.pop_back();

    just.remove_equality();
    just.remove_equality();
    return true;
}

bool simple_adt_solver::add_root(term_instance* b, term_instance* newRoot, bool incIneq) {
    assert(b->is_root());
    assert(newRoot->is_root());
    unsigned prevCnt = newRoot->cnt;
    propagator().add_undo([b, newRoot, prevCnt]() {
        b->parent = b;
        newRoot->cnt = prevCnt;
    });
    b->parent = newRoot;
    newRoot->cnt += b->cnt;

    justification just;
    if (!check_cycle(newRoot, just))
        return false;
    assert(just.empty());
    if (b->t->is_const() && !check_cycle(b, just))
        // Required for eg. x = f(a), x = f(x) <- the second would be immediately merged and we would only check f(a) for a cycle
        return false;

    unsigned prevSmallerSize = newRoot->smaller.size();
    unsigned prevGreaterSize = newRoot->greater.size();
    propagator().add_undo([newRoot, prevSmallerSize, prevGreaterSize]() {
        newRoot->smaller.resize(prevSmallerSize);
        newRoot->greater.resize(prevGreaterSize);
    });

    add_range(newRoot->smaller, b->smaller);
    add_range(newRoot->greater, b->greater);

    if (complexSolver.propagator().is_adt_split()) {
        /*unsigned prevIdx = b->eq_split_watches_idx;
        propagator().add_undo([b, prevIdx]() { b->eq_split_watches_idx = prevIdx; });
        for (; b->eq_split_watches_idx < b->eq_split_watches.size(); b->eq_split_watches_idx++) {
            auto watch = b->eq_split_watches[b->eq_split_watches_idx];
            if (!unify_split(watch.LHS, watch.RHS, watch.just))
                return false;
        }*/
        unsigned prevIdx = b->diseq_split_watches_idx;
        unsigned cnt = b->diseq_split_watches.size();
        propagator().add_undo([b, prevIdx]() { b->diseq_split_watches_idx = prevIdx; });
        for (; b->diseq_split_watches_idx < cnt; b->diseq_split_watches_idx++) {
            auto watch = b->diseq_split_watches[b->diseq_split_watches_idx];
            if (!non_unify_split(watch.LHS, watch.RHS, watch.just))
                return false;
        }

        prevIdx = newRoot->diseq_split_watches_idx;
        cnt = newRoot->diseq_split_watches.size();
        propagator().add_undo([newRoot, prevIdx]() { newRoot->diseq_split_watches_idx = prevIdx; });
        for (; newRoot->diseq_split_watches_idx < cnt; newRoot->diseq_split_watches_idx++) {
            auto watch = newRoot->diseq_split_watches[newRoot->diseq_split_watches_idx];
            if (!non_unify_split(watch.LHS, watch.RHS, watch.just))
                return false;
        }
    }
    else {
        if (!update_diseq(b, newRoot))
            return false;
    }
    if (incIneq) {
        if (!update_ineq(newRoot))
            return false;
    }
    // Don't use foreach - we might change the vector
    for (int i = 0; i < newRoot->smaller_watches.size(); i++) {
        auto [lhs, rhs, eq, just2] = newRoot->smaller_watches[i];
        less(just2, lhs, rhs, eq);
    }
    return true;
}

bool simple_adt_solver::merge_root(term_instance* r1, term_instance* r2, const equality& eq, bool incIneq) {
    assert(r1->is_root());
    assert(r2->is_root());
    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID)
        return false;

    auto* lhs = eq.LHS;
    auto* rhs = eq.RHS;
    const unsigned prev1 = lhs->actual_connections.size();
    const unsigned prev2 = rhs->actual_connections.size();

    lhs->actual_connections.push_back(eq);
    rhs->actual_connections.push_back(eq);

    propagator().add_undo([lhs, rhs, prev1, prev2]() {
        lhs->actual_connections.pop_back();
        rhs->actual_connections.pop_back();
        assert(lhs->actual_connections.size() == prev1);
        assert(rhs->actual_connections.size() == prev2);
    });

    if (r1->t->is_const() != r2->t->is_const())
        // Prefer constant roots
        return r1->t->is_const()
               ? add_root(r2, r1, incIneq)
               : add_root(r1, r2, incIneq);

    return r1->cnt > r2->cnt
           ? add_root(r2, r1, incIneq)
           : add_root(r1, r2, incIneq);
}

void simple_adt_solver::find_just(term_instance* n1, term_instance* n2, justification& minimalJust) {
    if (n1 == n2)
        return;
    std::deque<tuple<term_instance*, term_instance*, equality>> todo;
    std::unordered_map<term_instance*, equality> prev;
    prev.reserve(n1->actual_connections.size());

    for (auto& c : n1->actual_connections) {
        auto* to = c.GetOther(n1);
        if (n2 == to) {
            minimalJust.add(c.just);
            return;
        }
        todo.emplace_back(n1, to, c);
    }

    while (!todo.empty()) {
        auto [from, to, eq] = todo.front();
        todo.pop_front();
        if (!prev.insert(make_pair(to, eq)).second)
            continue;
        if (n2 == to) {
            minimalJust.add(eq.just);

            while (from != n1) {
                auto n = prev[from];
                from = n.GetOther(from);
                minimalJust.add(n.just);
            }
            return;
        }
        for (auto& equality : to->actual_connections) {
            auto* next = equality.GetOther(to);
            todo.emplace_back(to, next, equality);
        }
    }

    throw solving_exception("Proof seems to be wrong");
}
