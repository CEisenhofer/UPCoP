#include "matrix_propagator.h"

static unsigned conflicts = 0;

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
    clause_instance* lhsInfo;
    clause_instance* rhsInfo;

    if (!tryGetValue(exprToEq, e, info)) {
        less_than info2;
        if (!isTrue || !tryGetValue(exprToLess, e, info2))
            return false;

        lhsInfo = info2.LHS->origin;
        rhsInfo = info2.RHS->origin;
        if ((lhsInfo != nullptr && lhsInfo->value == unsat) || (rhsInfo != nullptr && rhsInfo->value == unsat)) {
            LogN("Dropped");
            return false;
        }
        if (lhsInfo != nullptr && lhsInfo->value == undef) {
            LogN("Shelved");
            lhsInfo->delayedRelevantLess.push_back(info2);
            propagator().add_undo([lhsInfo]() { lhsInfo->delayedRelevantLess.pop_back(); });
            return true;
        }
        if (rhsInfo != nullptr && rhsInfo->value == undef) {
            LogN("Shelved");
            rhsInfo->delayedRelevantLess.push_back(info2);
            propagator().add_undo([rhsInfo]() { rhsInfo->delayedRelevantLess.pop_back(); });
            return true;
        }
        LogN("Processed");

        try {
            asserted_less(e, info2.LHS, info2.RHS);
        }
        catch (...) {
            cout << "Crashed test_less" << endl;
            exit(133);
        }
        return true;
    }
    assert(info.just.litJust.size() == 1 && info.just.eqJust.empty() && info.just.litJust[0] == e);

    lhsInfo = info.LHS->origin;
    rhsInfo = info.RHS->origin;
    assert(!(info.LHS->t->is_const() && info.RHS->t->is_const()));
    assert(lhsInfo != nullptr || rhsInfo != nullptr);

    if ((lhsInfo != nullptr && lhsInfo->value == unsat) || (rhsInfo != nullptr && rhsInfo->value == unsat)) {
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
        asserted_eq(e, info.LHS, info.RHS, isTrue);
    }
    catch (...) {
        cout << "Crashed unify" << endl;
        exit(132);
    }
    return true;
}

bool complex_adt_solver::asserted_eq(literal e, term_instance* lhs, term_instance* rhs, bool isTrue) const {
    assert(&lhs->t->Solver == &rhs->t->Solver);
    bool res;
    start_watch(term_time);
    if (propagator().is_adt_split()) {
        res = isTrue
               ? //lhs->t->Solver.unify_split(e, lhs, rhs)
               lhs->t->Solver.unify(e, lhs, rhs)
               : lhs->t->Solver.non_unify_split(prop->m.mk_not(e), lhs, rhs);
    }
    else {
        res = isTrue
              ? lhs->t->Solver.unify(e, lhs, rhs)
              : lhs->t->Solver.non_unify(prop->m.mk_not(e), lhs, rhs);
    }
    stop_watch(term_time);
    return res;
}

bool complex_adt_solver::asserted_less(literal e, term_instance* lhs, term_instance* rhs) const {
    assert(&lhs->t->Solver == &rhs->t->Solver);
    start_watch(term_time);
    bool res = lhs->t->Solver.less(e, lhs, rhs);
    stop_watch(term_time);
    return res;
}

bool complex_adt_solver::contains_cycle(term_instance* t, term_instance* c) const {
    assert(c->t->is_const());
    assert(t->t->is_var());
    stack<term_instance*> stack;
    stack.push(c);
    while (!stack.empty()) {
        auto* current = stack.top();
        stack.pop();
        if (current->t->is_ground())
            continue;
        if (current->t->is_const()) {
            for (auto* arg : current->t->Args) {
                stack.push(arg->get_instance(current->cpy_idx(), propagator()));
            }
            continue;
        }
        if (current == t)
            return true;
    }
    return false;
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
                stack.emplace(lhs2->get_arg(i, propagator()), rhs2->get_arg(i, propagator()));
            }
        }
        else {
            if (lhs2->t->is_var() && rhs2->t->is_var()) {
                subproblems.emplace_back(lhs2, rhs2);
                continue;
            }
            if ((lhs2->t->is_const() && !contains_cycle(rhs2, lhs2)) ||
                (rhs2->t->is_const() && !contains_cycle(lhs2, rhs2)))
                subproblems.emplace_back(lhs2, rhs2);
            else
                return false;
        }
    }
    return true;
}

bool complex_adt_solver::preprocess_less(stack<less_than> stack, vector<less_than>& subproblems, bool& eq) {

    while (!stack.empty()) {
        auto& current = stack.top();
        auto* lhs = current.LHS;
        auto* rhs = current.RHS;
        stack.pop();

        if (lhs == rhs)
            return !subproblems.empty();

        if (lhs->t->is_const() && rhs->t->is_const()) {
            if (lhs->t->FuncID != rhs->t->FuncID) {
                if (lhs->t->FuncID < rhs->t->FuncID) {
                    eq = true;
                    return true;
                }
                eq = false;
                return !subproblems.empty();
            }
            for (unsigned i = lhs->t->Args.size(); i > 0; i--) {
                stack.emplace(lhs->get_arg(i - 1, propagator()), rhs->get_arg(i - 1, propagator()));
            }
            continue;
        }
        subproblems.emplace_back(lhs, rhs);
    }
    return true;
}

literal complex_adt_solver::make_equality_atom(term_instance* lhs, term_instance* rhs) {
    assert(!lhs->t->is_const() || !rhs->t->is_const());
    assert(lhs != rhs);

    equality eq(lhs, rhs);
    formula expr = nullptr;

    if (!tryGetValue(eqToExpr, eq, expr)) {
        expr = prop->m.mk_lit(prop->new_observed_var(OPT(eq.to_string())));
        eq.just.add_literal((literal)expr);
        exprToEq.insert(make_pair((literal)expr, eq));
        eqToExpr.insert(make_pair(eq, expr));
    }
    assert(contains_key(eqToExpr, eq));
    assert(expr->is_literal());

    return (literal)expr;
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
        expr = make_equality_atom(eq2.LHS, eq2.RHS);
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

literal complex_adt_solver::make_less_atom(term_instance* lhs, term_instance* rhs) {
    assert(!lhs->t->is_const() || !rhs->t->is_const());
    assert(lhs != rhs);

    less_than lt(lhs, rhs);
    formula ltExpr = nullptr;

    if (!tryGetValue(lessToExpr, lt, ltExpr)) {
        ltExpr = prop->m.mk_lit(prop->new_observed_var(OPT(lt.to_string())));
        exprToLess.insert(make_pair((literal)ltExpr, lt));
        lessToExpr.insert(make_pair(lt, ltExpr));

        less_than gt(rhs, lhs);
        assert(!contains_key(lessToExpr, gt));

        literal gtExpr = prop->m.mk_lit(prop->new_observed_var(OPT(gt.to_string())));
        exprToLess.insert(make_pair((literal)gtExpr, gt));
        lessToExpr.insert(make_pair(gt, gtExpr));

        literal eqExpr = make_equality_atom(lhs, rhs);

        auto& prop = propagator();
        // !(x < y) <=> (x = y || y < x) and
        // !(y < x) <=> (x = y || x < y)
        // Very interestingly, CoPilot filled out all these propagations correctly automatically without the above comment (impressive!)
        prop.hard_propagate({}, prop.m.mk_or({ ltExpr, gtExpr, eqExpr }));
        prop.hard_propagate({}, prop.m.mk_or({ prop.m.mk_not(ltExpr), prop.m.mk_not(gtExpr) }));
        prop.hard_propagate({}, prop.m.mk_or({ prop.m.mk_not(ltExpr), prop.m.mk_not(eqExpr) }));
        prop.hard_propagate({}, prop.m.mk_or({ prop.m.mk_not(gtExpr), prop.m.mk_not(eqExpr) }));
    }

    assert(contains_key(lessToExpr, lt));
    assert(contains_key(lessToExpr, { rhs, lhs }));
    assert(ltExpr->is_literal());

    return (literal)ltExpr;
}

formula complex_adt_solver::make_less_expr(vector<less_than> subproblems, bool eq) {
    vector<formula> cases;
    const unsigned sz = subproblems.size();
    cases.reserve(sz + (unsigned)eq);

    for (unsigned i = 0; i < sz; i++) {
        vector<formula> cases2;
        cases2.reserve(i + 1);
        for (unsigned j = 0; j < i; j++) {
            cases2.push_back(make_equality_expr(subproblems[j].LHS, subproblems[j].RHS));
        }

        formula expr = make_less_atom(subproblems[i].LHS, subproblems[i].RHS);

        cases2.push_back(expr);
        cases.push_back(propagator().m.mk_and(cases2));
    }
    if (eq) {
        vector<formula> cases2;
        cases2.reserve(sz);
        for (int i = 0; i < sz; i++) {
            cases2.push_back(make_equality_expr(subproblems[i].LHS, subproblems[i].RHS));
        }
        cases.push_back(propagator().m.mk_and(cases2));
    }

    return prop->m.mk_or(cases);
}

formula complex_adt_solver::make_less_expr(term_instance* lhs, term_instance* rhs) {
    less_than lt(lhs, rhs);
    formula expr = nullptr;
    if (tryGetValue(lessToExpr, lt, expr))
        return expr;

    vector<less_than> subproblems;
    bool eq = false;
    if (!preprocess_less(lhs, rhs, subproblems, eq)) {
        expr = prop->m.mk_false();
        lessToExpr.insert(make_pair(lt, expr));
        return expr;
    }
    expr = make_less_expr(std::move(subproblems), eq);
    lessToExpr.insert(make_pair(lt, expr));
    return expr;
}

formula complex_adt_solver::make_greater_eq_expr(term_instance* lhs, term_instance* rhs) {
    return propagator().m.mk_not(make_less_eq_expr(rhs, lhs));
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

string simple_adt_solver::to_string() const {
    stringstream sb;
    for (int i = 0; i < funcNames.size(); i++) {
        sb << funcNames[i] << '/' << std::to_string(domains[i].size());
    }
    return sb.str();
}

bool simple_adt_solver::non_unify_split(literal just, term_instance* lhs, term_instance* rhs) {
    switch (test_non_unify_split(just, lhs, rhs)) {
        case sat:
            return true;
        case unsat:
            return false;
        default:
            // We need to observe only one side (we don't care if it is a constant, as we would also get merge callbacks on them)
            // just take the lhs
            lhs->diseq_split_watches.emplace_back(lhs, rhs, just);
            propagator().add_undo([lhs]() { lhs->diseq_split_watches.pop_back(); });
            return true;
    }
}

tri_state simple_adt_solver::test_non_unify_split(literal lit, term_instance* lhs, term_instance* rhs) {
    assert(!lhs->t->is_const() || !rhs->t->is_const()); // Why would the simplifier fail?
    auto* r1 = lhs->find_root(propagator());
    auto* r2 = rhs->find_root(propagator());

    if (r1 == r2) {
        justification justList;
        justList.add_literal(lit);
        justList.add_equality(lhs, rhs);
        conflict(justList);
        return unsat;
    }

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID)
            return sat;

        formula f = complexSolver.make_disequality_expr(r1, r2);
        if (f->is_true())
            return sat;
        justification justList;
        justList.add_literal(lit);
        justList.add_equality(lhs, r1);
        justList.add_equality(rhs, r2);

        if (f->is_false()) {
            conflict(justList);
            return unsat;
        }
        propagate(justList, f);
        return sat;
    }
    return undef;
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
            if (!are_equal(r1->get_arg(i, propagator()), r2->get_arg(i, propagator())))
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

    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const()) {
        justifications.add_equality(lhs, r1);
        justifications.add_equality(rhs, r2);
        if (r1->t->FuncID != r2->t->FuncID) {
            conflict(justifications);
            return false;
        }
        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            if (!unify(r1->get_arg(i, propagator()), r2->get_arg(i, propagator()), justifications))
                return false;
        }
        justifications.remove_equality();
        justifications.remove_equality();
        return true;
    }

    if (merge_root(r1, r2, { lhs, rhs, { justifications } })) {
        return true;
    }
    justifications.add_equality(lhs, r1);
    justifications.add_equality(rhs, r2);
    conflict(justifications);
    return false;
}

z3::check_result simple_adt_solver::non_unify(Lazy* lazy) {
    if (lazy->Solved)
        return z3::check_result::sat;
    // TODO: This does not guarantee best conflicts
    // f(x, y) != f(x', y'), x = a, x = x', y = b, y' = c -- this would contain "a" in the conflict although irrelevant
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
            lazy->LHS = current.lhs->get_arg(current.argIdx, propagator());
            lazy->RHS = current.rhs->get_arg(current.argIdx, propagator());
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
            lazy->LHS = r1->get_arg(0, propagator());
            lazy->RHS = r2->get_arg(0, propagator());
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

bool simple_adt_solver::check_containment_cycle(term_instance* inst) {
    if (!inst->t->is_const() || inst->t->is_ground())
        return true;
    auto* r = inst->find_root(propagator());
    justification justifications;
    justifications.add_equality(inst, r);
    for (auto* arg : inst->t->Args) {
        if (!check_containment_cycle(arg->get_instance(inst->cpy_idx(), propagator()), r, justifications))
            return false;
    }
    return true;
}

bool simple_adt_solver::check_containment_cycle(term_instance* inst, term_instance* search, justification& justifications) {
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
        if (!check_containment_cycle(arg->get_instance(r->cpy_idx(), propagator()), search, justifications))
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

bool simple_adt_solver::less(literal just, term_instance* lhs, term_instance* rhs) {

    justification j;
    j.add_literal(just);

    start_mark();
    if (!check_smaller_cycle(rhs, rhs->find_root(propagator()), lhs, j)) {
        conflict(j);
        end_mark();
        return false;
    }
    end_mark();

    start_mark();
    if (!is_reachable(lhs->find_root(propagator()), rhs->find_root(propagator()))) {
        // redundant
        end_mark();
        return false;
    }
    end_mark();

    switch (test_less(just, lhs, rhs)) {
        case sat:
            return true;
        case unsat:
            return false;
        default: {
            lhs->smaller_watches.emplace_back(lhs, rhs, just);
            rhs->smaller_watches.emplace_back(lhs, rhs, just);
            unsigned prevSmallerCnt = rhs->smaller.size();
            rhs->smaller.emplace_back(lhs, just);

            propagator().add_undo([lhs, rhs, prevSmallerCnt]() {
                lhs->smaller_watches.pop_back();
                rhs->smaller_watches.pop_back();
                rhs->smaller.pop_back();
                assert(rhs->smaller.size() == prevSmallerCnt);
            });
            return true;
        }
    }
}

tri_state simple_adt_solver::test_less(literal just, term_instance* lhs, term_instance* rhs) {

    auto* r1 = lhs->find_root(propagator());
    auto* r2 = rhs->find_root(propagator());

    if (r1 == r2) {
        justification j;
        j.add_literal(just);
        j.add_equality(lhs, rhs);
        conflict(j);
        return unsat;
    }

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            if (r1->t->FuncID < r2->t->FuncID)
                return sat;
            assert(r1->t->FuncID > r2->t->FuncID);
            justification justList;
            justList.add_literal(just);
            justList.add_equality(lhs, r1);
            justList.add_equality(rhs, r2);
            conflict(justList);
            return unsat;
        }

        assert(!r1->t->Args.empty());

        formula f = complexSolver.make_less_expr(r1, r2);
        if (f->is_true())
            return sat;
        justification justList;
        justList.add_literal(just);
        justList.add_equality(lhs, r1);
        justList.add_equality(rhs, r2);

        if (f->is_false()) {
            conflict(justList);
            return unsat;
        }
        propagate(justList, f);
        return sat;
    }
    return undef;
}

bool simple_adt_solver::is_reachable(term_instance* from, term_instance* to) {
    assert(from->is_root());
    assert(to->is_root());

    if (from == to)
        return true;

    term_instance* current2 = to;
    do {
        const unsigned cnt = current2->smaller.size();
        auto& children = current2->smaller;

        for (auto i = 0; i < cnt; i++) {
            if (!is_reachable(from, children[i].first->find_root(propagator())))
                return false;
        }
        current2 = current2->next_sibling;
    } while (current2 != to);
    return true;
}

// does not add conflicts - has to be done separately!!
bool simple_adt_solver::check_smaller_cycle(term_instance* start, term_instance* startRoot, term_instance* current, justification& just) {
    assert(startRoot->is_root());
    assert(start->find_root((propagator_base&)propagator()) == startRoot);

    auto* currentRoot = current->find_root((propagator_base&)propagator());

    if (startRoot == currentRoot) {
        just.add_equality(start, current);
        return false;
    }

    // TODO: Not sure that we need this check - Update: Yes, we do but maybe not the one in test_less
    if (startRoot->t->is_const() && currentRoot->t->is_const() &&
        startRoot->t->FuncID != currentRoot->t->FuncID &&
        startRoot->t->FuncID < currentRoot->t->FuncID) {
        just.add_equality(start, startRoot);
        just.add_equality(current, currentRoot);
        return false;
    }

    term_instance* current2 = current;
    do {

        const unsigned cnt = current2->smaller.size();
        auto& children = current2->smaller;

        for (auto i = 0; i < cnt; i++) {
            auto& [inst, justifications] = children[i];

            just.add_equality(current, current2);
            just.add_literal(justifications);
            if (!check_smaller_cycle(start, startRoot, inst, just))
                return false;
            just.litJust.pop_back();
            just.eqJust.pop_back();
        }

        current2 = current2->next_sibling;
    } while (current2 != current);
    return true;
}

bool simple_adt_solver::check_diseq_replacement(term_instance* newRoot) {
    auto* current = newRoot;
    do {
        unsigned startWatch = current->diseq_split_watches_idx;
        for (unsigned i = current->diseq_split_watches_idx; i < current->diseq_split_watches.size(); i++) {
            auto watch = current->diseq_split_watches[i];
            switch (test_non_unify_split(watch.just, watch.LHS, watch.RHS)) {
                case unsat:
                    return false;
                case undef:
                    break;
                default: {
                    unsigned swpIdx = current->diseq_split_watches_idx++;
                    std::swap(current->diseq_split_watches[swpIdx], current->diseq_split_watches[i]);
                    propagator().add_undo([current, swpIdx, i]() { std::swap(current->diseq_split_watches[swpIdx], current->diseq_split_watches[i]); });
                    break;
                }
            }
        }
        if (startWatch != current->diseq_split_watches_idx)
            propagator().add_undo([current, startWatch]() { current->diseq_split_watches_idx = startWatch; });

        current = current->next_sibling;
    } while (current != newRoot);
    return true;
}

bool simple_adt_solver::check_less_replacement(term_instance* newRoot) {
    auto* current = newRoot;
    do {
        unsigned startWatch = current->smaller_watches_idx;
        for (unsigned i = current->smaller_watches_idx; i < current->smaller_watches.size(); i++) {
            auto [lhs, rhs, just2] = current->smaller_watches[i];
            switch (test_less(just2, lhs, rhs)) {
                case unsat:
                    return false;
                case undef:
                    break;
                default: {
                    unsigned swpIdx = current->smaller_watches_idx++;
                    std::swap(current->smaller_watches[swpIdx], current->smaller_watches[i]);
                    propagator().add_undo([current, swpIdx, i]() { std::swap(current->smaller_watches[swpIdx], current->smaller_watches[i]); });
                    break;
                }
            }
        }
        if (startWatch != current->smaller_watches_idx)
            propagator().add_undo([current, startWatch]() { current->smaller_watches_idx = startWatch; });

        current = current->next_sibling;
    } while (current != newRoot);
    return true;
}

bool simple_adt_solver::add_root(term_instance* b, term_instance* newRoot, const equality& eq) {
    assert(b->is_root());
    assert(newRoot->is_root());
    assert(b != newRoot); // this is important, as the internal dependency graph has to be spanning to use depth-first search for justifications

    // we have to postpone the conflict until we actually merged the eq-classes
    justification just;
    bool succ = check_smaller_cycle(eq.LHS, eq.LHS->find_root(propagator()), eq.RHS, just);
    if (succ) {
        assert(just.empty());
        succ = check_smaller_cycle(eq.RHS, eq.RHS->find_root(propagator()), eq.LHS, just);
    }

    unsigned prevCnt = newRoot->cnt;

    auto* p = newRoot->prev_sibling;
    auto* n = b->next_sibling;

    b->next_sibling = newRoot;
    newRoot->prev_sibling = b;

    p->next_sibling = n;
    n->prev_sibling = p;

    propagator().add_undo([b, newRoot, p, n, prevCnt]() {
        b->parent = b;
        newRoot->cnt = prevCnt;

        newRoot->prev_sibling = p;
        p->next_sibling = newRoot;

        b->next_sibling = n;
        n->prev_sibling = b;
    });
    b->parent = newRoot;
    newRoot->cnt += b->cnt;

    if (!succ) {
        // now it is safe to report the conflict
        just.add_equality(eq.LHS, eq.RHS);
        conflict(just);
        return false;
    }

    if (!check_containment_cycle(newRoot))
        return false;

    if (complexSolver.propagator().is_adt_split()) {
        if (!check_diseq_replacement(newRoot))
            return false;
    }
    else {
        if (!update_diseq(b, newRoot))
            return false;
    }
    if (!check_less_replacement(newRoot))
        return false;
    return true;
}

bool simple_adt_solver::merge_root(term_instance* r1, term_instance* r2, const equality& eq) {
    assert(r1->is_root());
    assert(r2->is_root());
    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID) {
        assert(false); // Why would that happen; unify would have made a very bad job
        return false;
    }

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
               ? add_root(r2, r1, eq)
               : add_root(r1, r2, eq);

    return r1->cnt > r2->cnt
           ? add_root(r2, r1, eq)
           : add_root(r1, r2, eq);
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
