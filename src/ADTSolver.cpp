#include "propagator_base.h"

ComplexADTSolver::~ComplexADTSolver() {
    for (auto& solver: Solvers) {
        delete solver;
    }
}

void ComplexADTSolver::reset(propagator_base* propagator) {
    prop = propagator;
    interpretation.clear();
    exprToEq.clear();
    exprToLess.clear();
    eqToExpr.clear();
    lessToExpr.clear();

    for (const auto* s : Solvers) {
        for (auto term : s->hashCon) {
            term.second->reset();
        }
    }
}

SimpleADTSolver* ComplexADTSolver::NewSolver(const string& name) {
    auto* adtSolver = new SimpleADTSolver(*this, Solvers.size());
    nameToSolver.insert(make_pair(name, adtSolver));
    Solvers.push_back(adtSolver);
    SortNames.push_back(name);
    return adtSolver;
}

SimpleADTSolver* ComplexADTSolver::GetSolver(const string& name) {
    SimpleADTSolver* solver = nullptr;
    return tryGetValue(nameToSolver, name, solver) ? solver : NewSolver(name);
}

static int inv_cnt = 0;

bool ComplexADTSolver::Asserted(literal e, bool isTrue) {
    equality info;
    if (!tryGetValue(exprToEq, e, info))
        return false;
    inv_cnt++;
    interpretation.insert(make_pair(e, isTrue));
    prop->add_undo([this, e]() { interpretation.erase(e); });
    assert(info.just.size() == 1 && typeid(*(info.just[0])) == typeid(LiteralJustification) &&
           ((LiteralJustification*) info.just[0])->lit == e);
    try {
        Asserted(e, info.LHS, info.RHS, isTrue);
    }
    catch (...) {
        cout << "Crashed Unify" << endl;
        exit(132);
    }
    return true;
}

bool ComplexADTSolver::Asserted(literal e, term_instance* lhs, term_instance* rhs, bool isTrue) const {
    assert(&lhs->t->Solver == &rhs->t->Solver);
    return isTrue
           ? lhs->t->Solver.Unify(e, lhs, rhs)
           : lhs->t->Solver.NonUnify(prop->m.mk_not(e), lhs, rhs);
}

literal ComplexADTSolver::MakeEqualityExpr(term_instance* lhs, term_instance* rhs) {
    if (lhs->t->HashID == rhs->t->HashID && (lhs->cpyIdx == rhs->cpyIdx || lhs->t->Ground))
        return prop->m.mk_true();

    equality eq(lhs, rhs, vector<Justification*>());

    literal expr = nullptr;
    if (tryGetValue(eqToExpr, eq, expr))
        return expr;
    expr = prop->m.mk_lit(prop->new_observed_var(OPT(eq.to_string())));
    eq.just.push_back(new LiteralJustification(expr));
    exprToEq.insert(make_pair(expr, eq));
    eqToExpr.insert(make_pair(eq, expr));
    return expr;
}

literal ComplexADTSolver::MakeDisEqualityExpr(term_instance* lhs, term_instance* rhs) {
    return prop->m.mk_not(MakeEqualityExpr(lhs, rhs));
}

literal ComplexADTSolver::MakeLessExpr(term_instance* lhs, term_instance* rhs) {
    if (lhs->t->HashID == rhs->t->HashID && (lhs->cpyIdx == rhs->cpyIdx || lhs->t->Ground))
        return prop->m.mk_false();
    if (lhs->t->is_const() == rhs->t->is_const()) {
        // TODO: Proper preprocessing
        if (lhs->t->FuncID < rhs->t->FuncID)
            return prop->m.mk_true();
        if (lhs->t->FuncID > rhs->t->FuncID)
            return prop->m.mk_false();
    }

    lessThan le(lhs, rhs);

    literal expr = nullptr;
    if (tryGetValue(lessToExpr, le, expr))
        return expr;
    expr = prop->m.mk_lit(prop->new_observed_var(OPT(le.to_string())));
    exprToLess.insert(make_pair(expr, le));
    lessToExpr.insert(make_pair(le, expr));
    return expr;
}

literal ComplexADTSolver::MakeGreaterEqExpr(term_instance* lhs, term_instance* rhs) {
    return prop->m.mk_not(MakeLessExpr(lhs, rhs));
}

void ComplexADTSolver::PeekTerm(const string& solver, const string& name, int argCnt) {
    GetSolver(solver)->PeekTerm(name, argCnt);
}

bool ComplexADTSolver::AreEqual(term_instance* lhs, term_instance* rhs) {
    return lhs->t->Solver.SolverId == rhs->t->Solver.SolverId && lhs->t->Solver.AreEqual(lhs, rhs);
}

SimpleADTSolver::~SimpleADTSolver() {
    for (auto& list: hashCon) {
        delete list.second;
    }
}

void SimpleADTSolver::Conflict(const vector<Justification*>& just) {
    if (propagator().is_conflict())
        return;
    vector<literal> justExpr;
    for (auto* j: just) {
        j->AddJustification(this, justExpr);
    }
    propagator().propagate_conflict(justExpr);
}

void SimpleADTSolver::Propagate(const vector<Justification*>& just, formula prop) {
    if (propagator().is_conflict())
        return;
    vector<literal> justExpr;
    for (auto* j: just) {
        j->AddJustification(this, justExpr);
    }
    propagator().hard_propagate(justExpr, prop);
}

string SimpleADTSolver::PrettyPrint(const term* t, unsigned cpyIdx,
                                    unordered_map<term_instance*, string>* prettyNames) const {
    if (t->FuncID < 0) {
        if (prettyNames == nullptr)
            return "var " + VarNames[-t->FuncID - 1];
        string name;
        if (tryGetValue(*prettyNames, t->GetInstance(cpyIdx), name))
            return name;
        prettyNames->insert(make_pair(t->GetInstance(cpyIdx), name = "$" + std::to_string(prettyNames->size())));
        return name;
    }

    if (t->Args.empty())
        return FuncNames[t->FuncID];
    std::stringstream sb;
    sb << FuncNames[t->FuncID];
    sb << '(' << PrettyPrint(t->Args[0], cpyIdx, prettyNames);
    for (int i = 1; i < t->Args.size(); i++) {
        sb << ',' << PrettyPrint(t->Args[i], cpyIdx, prettyNames);
    }
    sb << ')';
    return sb.str();
}

int SimpleADTSolver::PeekTerm(const string& name, unsigned argCnt) {
    std::vector<unsigned> domain(argCnt, SolverId);
    return PeekTerm(name, std::move(domain));
}

int SimpleADTSolver::PeekTerm(const string& name, vector<unsigned> domain) {
    int id = 0;
    if (!tryGetValue(nameToId, name, id)) {
        id = (int) FuncNames.size();
        Domains.push_back(std::move(domain));
        FuncNames.push_back(name);
        nameToId.insert(make_pair(name, id));
    }
    if (id < 0)
        throw solving_exception("Name already used by variable");
    return id;
}

term* SimpleADTSolver::MakeTerm(int id, const pvector<term>& args) {
    assert(id >= 0);
    if (id >= FuncNames.size())
        throw solving_exception("Term index out of bounds");
    return MakeTermInternal(id, args);
}

term* SimpleADTSolver::MakeTermInternal(int id, const pvector<term>& args) {
    const RawTermWrapper key(new raw_term(id, args));
    term* t = nullptr;
    if (tryGetValue(hashCon, key, t)) {
        delete key.obj;
        return t;
    }
    delete key.obj;
    t = new term(id, args, *this, hashCon.size());
    hashCon.insert(make_pair(RawTermWrapper(t), t));
    return t;
}

term* SimpleADTSolver::MakeVar(const string& name) {
    int id = 0;
    if (!tryGetValue(nameToId, name, id)) {
        id = -((int) VarNames.size() + 1);
        VarNames.push_back(name);
        nameToId.insert(make_pair(name, id));
    }
    if (id >= 0)
        throw solving_exception("Name already used by function");
    return MakeVar(-id - 1);
}

term* SimpleADTSolver::MakeVar(int idx) {
    if (idx >= VarNames.size())
        throw solving_exception("Variable index out of bounds");
    return MakeTermInternal(-(idx + 1), {});
}

bool SimpleADTSolver::UpdateDiseq(term_instance* b, term_instance* newRoot) {
    assert(b->FindRootQuick(propagator()) == newRoot);
    for (auto& info: newRoot->diseq_watches) {
        if (NonUnify(info) == z3::check_result::unsat)
            // TODO: Swap remove if sat
            return false;
    }

    unsigned prevSize = newRoot->diseq_watches.size();
    propagator().add_undo([newRoot, prevSize]() {
        newRoot->diseq_watches.resize(prevSize);
    });

    for (auto& info: b->diseq_watches) {
        switch (NonUnify(info)) {
            case z3::check_result::unsat:
                return false;
            case z3::check_result::unknown:
                newRoot->diseq_watches.push_back(info);
                break;
        }
    }
    return true;
}

bool SimpleADTSolver::UpdateIneq(term_instance* newRoot) {
    assert(newRoot->is_root());
    unsigned cnt = newRoot->greater.size();
    for (auto i = 0; i < cnt; i++) {
        auto& [inst, eq, just] = newRoot->greater[i];
        vector<Justification*> j(just);
        vector<term_instance*> path;
        if (!Check(newRoot, inst, eq, j, path, false))
            return false;
    }
    cnt = newRoot->smaller.size();
    for (unsigned i = 0; i < cnt; i++) {
        auto& [inst, eq, just] = newRoot->smaller[i];
        vector<Justification*> j(just);
        vector<term_instance*> path;
        if (!Check(newRoot, inst, eq, j, path, true))
            return false;
    }
    return true;
}

string SimpleADTSolver::to_string() const {
    stringstream sb;
    for (int i = 0; i < FuncNames.size(); i++) {
        sb << FuncNames[i] << '/' << std::to_string(Domains[i].size());
    }
    return sb.str();
}

bool SimpleADTSolver::Unify(literal just, term_instance* lhs, term_instance* rhs) {
    vector<Justification*> justification{new LiteralJustification(just)};
    return Unify(lhs, rhs, justification);
}

bool SimpleADTSolver::AreEqual(term_instance* lhs, term_instance* rhs) {
    if (lhs->t->HashID == rhs->t->HashID && (lhs->cpyIdx == rhs->cpyIdx || lhs->t->Ground))
        return true;
    if (lhs->t->Ground && rhs->t->Ground && lhs->t->HashID != rhs->t->HashID)
        return false;
    term_instance* r1 = lhs->FindRootQuick(propagator());
    term_instance* r2 = rhs->FindRootQuick(propagator());
    if (r1 == r2)
        return true;
    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID)
            return false;
        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            if (!AreEqual(r1->t->Args[i]->GetInstance(r1->cpyIdx), r2->t->Args[i]->GetInstance(r2->cpyIdx)))
                return false;
        }
        return true;
    }
    return false;
}

bool SimpleADTSolver::Unify(term_instance* lhs, term_instance* rhs, vector<Justification*>& justifications) {

    if (lhs->t->HashID == rhs->t->HashID && (lhs->cpyIdx == rhs->cpyIdx || lhs->t->Ground))
        return true;
    if (lhs->t->Ground && rhs->t->Ground && lhs->t->HashID != rhs->t->HashID) {
        Conflict(justifications);
        return false;
    }

    term_instance* r1 = lhs->FindRootQuick(propagator());
    term_instance* r2 = rhs->FindRootQuick(propagator());
    justifications.push_back(new EqualityJustification(lhs, r1));
    justifications.push_back(new EqualityJustification(rhs, r2));

    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            Conflict(justifications);
            return false;
        }
        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            if (!Unify(r1->t->Args[i]->GetInstance(r1->cpyIdx), r2->t->Args[i]->GetInstance(r2->cpyIdx),
                       justifications))
                return false;
        }
        justifications.resize(justifications.size() - 2);
        return true;
    }

    vector<Justification*> justCpy;
    justCpy.reserve(justifications.size());
    for (const auto& j: justifications) {
        if (!j->is_tautology())
            justCpy.push_back(j);
    }

    equality equality(lhs, rhs, justCpy);
    if (MergeRoot(r1, r2, equality)) {
        justifications.resize(justifications.size() - 2);
        return true;
    }
    Conflict(justifications);
    return false;
}

z3::check_result SimpleADTSolver::NonUnify(Lazy* lazy) {
    if (lazy->Solved)
        return z3::check_result::sat;

    unsigned prevSize = lazy->Justifications.size();
    auto prevLHS = lazy->LHS, prevRHS = lazy->RHS;
    auto prevPrev = lazy->Prev;

    propagator().add_undo([lazy, prevSize, prevLHS, prevRHS, prevPrev]() {
        lazy->Justifications.resize(prevSize);
        lazy->LHS = prevLHS;
        lazy->RHS = prevRHS;
        lazy->Solved = false;
        lazy->Prev = prevPrev;
    });

    while (lazy->LHS != nullptr || !lazy->Prev.empty()) {
        if (lazy->LHS == nullptr) {
            // don't worry about undoing operations on lazy; we copy it anyway
            assert(lazy->RHS == nullptr);
            auto current = lazy->Prev.top();
            if (current.ArgIdx >= current.LHS->t->Args.size()) {
                lazy->Prev.pop();
                continue;
            }
            lazy->LHS = current.LHS->t->Args[current.ArgIdx]->GetInstance(current.LHS->cpyIdx);
            lazy->RHS = current.RHS->t->Args[current.ArgIdx]->GetInstance(current.RHS->cpyIdx);
            current.ArgIdx++;
        }

        assert(lazy->LHS != nullptr);
        assert(lazy->RHS != nullptr);

        term_instance* r1 = lazy->LHS->FindRootQuick(propagator());
        term_instance* r2 = lazy->RHS->FindRootQuick(propagator());
        if (r1 == r2) {
            lazy->Justifications.push_back(new EqualityJustification(lazy->LHS, lazy->RHS));
            lazy->LHS = nullptr;
            lazy->RHS = nullptr;
            continue;
        }
        if (r1->t->Ground && r2->t->Ground && r1->t->HashID != r2->t->HashID) {
            lazy->Solved = true;
            return z3::check_result::sat;
        }
        if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID) {
            lazy->Solved = true;
            return z3::check_result::sat;
        }

        if (r1->t->is_var() || r2->t->is_var()) {
            assert((lazy->LHS != nullptr && lazy->RHS != nullptr) || !lazy->Prev.empty());
            return z3::check_result::unknown;
        }

        assert(!r1->t->Args.empty());
        assert(r1->t->Args.size() == r2->t->Args.size());

        lazy->Justifications.push_back(new EqualityJustification(lazy->LHS, r1));
        lazy->Justifications.push_back(new EqualityJustification(lazy->RHS, r2));

        if (r1->t->Args.size() == 1) {
            lazy->LHS = r1->t->Args[0]->GetInstance(r1->cpyIdx);
            lazy->RHS = r2->t->Args[0]->GetInstance(r2->cpyIdx);
            continue;
        }

        lazy->LHS = nullptr;
        lazy->RHS = nullptr;

        lazy->Prev.emplace(r1, r2);
    }

    Conflict(lazy->Justifications);
    return z3::check_result::unsat;
}

bool SimpleADTSolver::CheckCycle(term_instance* inst, vector<Justification*>& justifications) {
    if (!inst->t->is_const() || inst->t->Ground)
        return true;
    auto* r = inst->FindRootQuick(propagator());
    justifications.push_back(new EqualityJustification(inst, r));
    for (auto* arg: inst->t->Args) {
        if (!CheckCycle(arg->GetInstance(inst->cpyIdx), r, justifications))
            return false;
    }
    justifications.pop_back();
    return true;
}

bool SimpleADTSolver::CheckCycle(term_instance* inst, term_instance* search, vector<Justification*>& justifications) {
    assert(search->is_root());
    auto* r = inst->FindRootQuick(propagator());

    if (r == search) {
        // Found the cycle
        justifications.push_back(new EqualityJustification(inst, r));
        Conflict(justifications);
        return false;
    }

    if (r->t->is_var())
        return true;

    justifications.push_back(new EqualityJustification(inst, r));
    for (auto* arg: r->t->Args) {
        if (!CheckCycle(arg->GetInstance(r->cpyIdx), search, justifications))
            return false;
    }
    justifications.pop_back();
    return true;
}

bool SimpleADTSolver::NonUnify(literal just, term_instance* lhs, term_instance* rhs) {
    Lazy* lazy = new Lazy(lhs, rhs);
    lazy->Justifications.push_back(new LiteralJustification(just));
    propagator().add_undo([lazy]() { delete lazy; });
    z3::check_result status = NonUnify(lazy);
    if (status == z3::check_result::sat || lazy->Solved)
        return true;
    if (status == z3::check_result::unsat)
        return false;

    assert(lazy->LHS != nullptr);

    auto* r = lazy->LHS->FindRootQuick(propagator());
    if (r->t->is_var()) {
        propagator().add_undo([r]() { r->diseq_watches.pop_back(); });
        r->diseq_watches.push_back(lazy);
        return true;
    }
    r = lazy->RHS->FindRootQuick(propagator());
    assert(r->t->is_var());
    propagator().add_undo([r]() { r->diseq_watches.pop_back(); });
    r->diseq_watches.push_back(lazy);
    return true;
}

bool SimpleADTSolver::Less(literal just, term_instance* lhs, term_instance* rhs, bool eq) {

    auto* r1 = lhs->FindRootQuick(propagator());
    auto* r2 = rhs->FindRootQuick(propagator());

    if (r1 == r2) {
        if (eq)
            return true;
        vector<Justification*> j;
        j.push_back(new LiteralJustification(just));
        j.push_back(new EqualityJustification(lhs, rhs));
        Conflict(j);
        return false;
    }

    unsigned prevGreaterCnt = r1->greater.size();
    unsigned prevSmallerCnt = r2->smaller.size();

    vector<Justification*> just1{new LiteralJustification(just)};
    vector<Justification*> just2{new LiteralJustification(just)};

    r1->greater.emplace_back(r2, eq, just1);
    r2->smaller.emplace_back(r1, eq, just2);

    propagator().add_undo([r1, r2, prevGreaterCnt, prevSmallerCnt]() {
        r1->greater.pop_back();
        r2->smaller.pop_back();
        assert(r1->greater.size() == prevGreaterCnt);
        assert(r2->smaller.size() == prevSmallerCnt);
    });

    vector<Justification*> j{new LiteralJustification(just)};
    vector<term_instance*> path;
    if (!Check(r1, r2, eq, j, path, false))
        return false;
    assert(path.empty());
    assert(j.size() == 1);
    if (!Check(r2, r1, eq, j, path, true))
        return false;

    if (r1->t->is_const() && r2->t->is_const()) {
        if (r1->t->FuncID != r2->t->FuncID) {
            if (r1->t->FuncID < r2->t->FuncID)
                return true;
            assert(r1->t->FuncID > r2->t->FuncID);
            vector<Justification*> justifications{
                    new LiteralJustification(just),
                    new EqualityJustification(lhs, r1),
                    new EqualityJustification(rhs, r2)
            };
            Conflict(justifications);
            return false;
        }

        assert(!r1->t->Args.empty());

        vector<formula> cases;
        cases.reserve(r1->t->Args.size() + (eq ? 1 : 0));

        for (unsigned i = 0; i < r1->t->Args.size(); i++) {
            vector<formula> cases2;
            cases2.reserve(i + 1);
            for (unsigned j = 0; j < i; j++) {
                cases2[j] = ComplexSolver.MakeEqualityExpr(
                        r1->t->Args[j]->GetInstance(r1->cpyIdx),
                        r2->t->Args[j]->GetInstance(r2->cpyIdx));
            }
            cases2[i] = ComplexSolver.MakeLessExpr(
                    r1->t->Args[i]->GetInstance(r1->cpyIdx),
                    r2->t->Args[i]->GetInstance(r2->cpyIdx));
            cases[i] = propagator().m.mk_and(cases2);
        }
        if (eq) {
            vector<formula> cases2;
            cases2.reserve(r1->t->Args.size());
            for (int i = 0; i < r1->t->Args.size(); i++) {
                cases2[i] = ComplexSolver.MakeEqualityExpr(
                        r1->t->Args[i]->GetInstance(r1->cpyIdx),
                        r2->t->Args[i]->GetInstance(r2->cpyIdx));
            }
            cases[r1->t->Args.size()] = propagator().m.mk_and(cases2);
        }
        vector<Justification*> justifications{
                new LiteralJustification(just),
                new EqualityJustification(lhs, r1),
                new EqualityJustification(rhs, r2)
        };
        Propagate(justifications, propagator().m.mk_or(cases));
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

bool SimpleADTSolver::Check(term_instance* start, term_instance* current, bool eq, vector<Justification*>& just,
                            vector<term_instance*>& path, bool smaller) {
    term_instance* r1 = start->FindRootQuick(propagator());
    term_instance* r2 = current->FindRootQuick(propagator());
    if (r1 == r2) {
        if (eq) {
            vector<Justification*> justCpy;
            justCpy.reserve(just.size());
            for (const auto& j: just) {
                if (!j->is_tautology())
                    justCpy.push_back(j);
            }
            for (auto* p: path) {
                equality equality(start, p, justCpy);
                MergeRoot(start, p, equality, false);
            }
            return true;
        }
        Conflict(just);
        return false;
    }
    just.push_back(new EqualityJustification(start, r1));
    just.push_back(new EqualityJustification(current, r2));
    if (start->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID &&
        smaller == (r1->t->FuncID < r2->t->FuncID)) {
        Conflict(just);
        return false;
    }
    if (eq)
        path.push_back(current);

    unsigned cnt = smaller ? r2->smaller.size() : r2->greater.size();
    for (auto i = 0; i < cnt; i++) {
        auto& [inst, b, justifications] = (smaller ? r2->smaller : r2->greater)[i];

        if (inst->FindRootQuick(propagator()) == r2) {
            assert(b);
            continue;
        }

        unsigned prev = just.size();
        add_range(just, justifications);
        if (!Check(r1, inst, eq && b, just, path, smaller))
            return false;
        just.resize(prev);
    }

    if (eq)
        path.pop_back();

    just.resize(just.size() - 2);
    return true;
}

bool SimpleADTSolver::AddRoot(term_instance* b, term_instance* newRoot, bool incIneq) {
    assert(b->is_root());
    assert(newRoot->is_root());
    unsigned prevCnt = newRoot->cnt;
    propagator().add_undo([b, newRoot, prevCnt]() {
        b->parent = b;
        newRoot->cnt = prevCnt;
    });
    b->parent = newRoot;
    newRoot->cnt += b->cnt;

    vector<Justification*> just;
    if (!CheckCycle(newRoot, just))
        return false;
    assert(just.empty());
    if (b->t->is_const() && !CheckCycle(b, just))
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

    if (!UpdateDiseq(b, newRoot))
        return false;
    if (incIneq) {
        if (!UpdateIneq(newRoot))
            return false;
    }
    for (int i = 0; i < newRoot->smaller_watches.size(); i++) {
        auto [lhs, rhs, eq, just] = newRoot->smaller_watches[i];
        Less(just, lhs, rhs, eq);
    }
    return true;
}

bool SimpleADTSolver::MergeRoot(term_instance* r1, term_instance* r2, equality& eq, bool incIneq) {
    assert(r1->is_root());
    assert(r2->is_root());
    if (r1 == r2)
        return true;

    if (r1->t->is_const() && r2->t->is_const() && r1->t->FuncID != r2->t->FuncID)
        return false;

    unsigned prev1 = eq.LHS->actual_connections.size();
    unsigned prev2 = eq.RHS->actual_connections.size();

    eq.LHS->actual_connections.push_back(eq);
    eq.RHS->actual_connections.push_back(eq);

    propagator().add_undo([eq, prev1, prev2]() {
        eq.LHS->actual_connections.pop_back();
        eq.RHS->actual_connections.pop_back();
        assert(eq.LHS->actual_connections.size() == prev1);
        assert(eq.RHS->actual_connections.size() == prev2);
    });

    if (r1->t->is_const() != r2->t->is_const())
        // Prefer constant roots
        return r1->t->is_const()
               ? AddRoot(r2, r1, incIneq)
               : AddRoot(r1, r2, incIneq);

    return r1->cnt > r2->cnt
           ? AddRoot(r2, r1, incIneq)
           : AddRoot(r1, r2, incIneq);
}

void SimpleADTSolver::FindJust(term_instance* n1, term_instance* n2, vector<Justification*>& minimalJust) {
    if (n1 == n2)
        return;
    std::deque<tuple<term_instance*, term_instance*, equality>> todo;
    std::unordered_map<term_instance*, equality> prev;

    for (auto& c: n1->actual_connections) {
        auto* to = c.GetOther(n1);
        if (n2 == to) {
            add_range(minimalJust, c.just);
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
            add_range(minimalJust, eq.just);

            while (from != n1) {
                auto n = prev[from];
                from = n.GetOther(from);
                add_range(minimalJust, n.just);
            }
            return;
        }
        for (auto& equality: to->actual_connections) {
            auto* next = equality.GetOther(to);
            todo.emplace_back(to, next, equality);
        }
    }

    throw solving_exception("Proof seems to be wrong");
}
