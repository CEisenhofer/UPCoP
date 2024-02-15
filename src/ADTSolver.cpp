#include "PropagatorBase.h"

size_t std::hash<equalityPair>::operator()(const equalityPair& x) const {
    return hash<Term>()(*x.lhs) * 133 + hash<Term>()(*x.rhs) * 233 + (size_t)x.lhsCpy * 31 + (size_t)x.rhsCpy;
}

ComplexADTSolver::ComplexADTSolver(bool z3Split) : SATSplit(z3Split) {}

ComplexADTSolver::~ComplexADTSolver() {
    for (auto& solver: Solvers) {
        delete solver;
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

bool ComplexADTSolver::Asserted(literal e, bool isTrue) {
    equalityPair* info = nullptr;
    if (!tryGetValue(exprToEq, e, info))
        return false;
    interpretation.insert(make_pair(e, isTrue));
    propagator->add_undo([this, e]() { interpretation.erase(e); });
    Asserted(e, info->lhs, info->lhsCpy, info->rhs, info->rhsCpy, isTrue);
    return true;
}

bool ComplexADTSolver::Asserted(literal e, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy, bool isTrue) {
    assert(&lhs->Solver == &rhs->Solver);
    return isTrue
           ? lhs->Solver.Unify(e, lhs, lhsCpy, rhs, rhsCpy)
           : lhs->Solver.NonUnify(e, lhs, lhsCpy, rhs, rhsCpy);
}

literal ComplexADTSolver::MakeEqualityExpr(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
    if (lhs->HashID == rhs->HashID && (lhsCpy == rhsCpy || lhs->Ground))
        return propagator->m.mk_true();

    // Important!
    if (lhs->HashID > rhs->HashID || (lhs->HashID == rhs->HashID && lhsCpy > rhsCpy)) {
        swap(lhs, rhs);
        swap(lhsCpy, rhsCpy);
    }
    literal l = nullptr;
    if (tryGetValue(eqToExpr, equalityPair(lhs, lhsCpy, rhs, rhsCpy), l))
        return l;
    l = propagator->m.mk_lit(propagator->new_observed_var(equalityPair(lhs, lhsCpy, rhs, rhsCpy).to_string()));
    exprToEq.insert(make_pair(l, equalityPair(lhs, lhsCpy, rhs, rhsCpy)));
    eqToExpr.insert(make_pair(equalityPair(lhs, lhsCpy, rhs, rhsCpy), l));
    return l;
}

literal ComplexADTSolver::MakeDisEqualityExpr(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
    return propagator->m.mk_not(MakeEqualityExpr(lhs, lhsCpy, rhs, rhsCpy));
}

void ComplexADTSolver::final() {
    for (auto& solver: Solvers) {
        solver->Final();
    }
}

void ComplexADTSolver::PeekTerm(const string& solver, const string& name, int argCnt) {
    GetSolver(solver)->PeekTerm(name, argCnt);
}

bool ComplexADTSolver::AreEqual(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
    return lhs->Solver.SolverId == rhs->Solver.SolverId && lhs->Solver.AreEqual(lhs, lhsCpy, rhs, rhsCpy);
}

string ComplexADTSolver::GetModel() const {
    std::stringstream sb;
    for (const auto& solver: Solvers) {
        sb << solver->GetModel() << '\n';
    }
    return sb.str();
}

void ComplexADTSolver::MakeZ3ADT(z3::context& ctx) {
    vector<vector<Z3_constructor>> constructors;
    constructors.reserve(SortNames.size());
    vector<Z3_symbol> constructor_names;
    constructor_names.reserve(SortNames.size());

    for (unsigned i = 0; i < Solvers.size(); i++) {
        auto& solver = *Solvers[i];
        constructor_names.push_back(Z3_mk_string_symbol(ctx, GetSolverName(i).c_str()));
        solver.EnsureFounded();
        constructors.emplace_back();
        constructors.back().reserve(solver.FuncNames.size());
        for (int j = 0; j < solver.FuncNames.size(); j++) {
            string funcName = solver.FuncNames[j];
            vector<unsigned>& domain = solver.Domains[j];
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
        Solvers[i]->Z3Sort = z3::sort(ctx, n_res[i]);
    }

    for (auto& list: constructors) {
        for (auto* c: list) {
            Z3_del_constructor(ctx, c);
        }
    }
    for (auto& list : constructorList) {
        Z3_del_constructor_list(ctx, list);
    }
}

z3::sort& ComplexADTSolver::GetZ3Sort(const string& name) {
    return *nameToSolver[name]->Z3Sort;
}

SimpleADTSolver::~SimpleADTSolver() {
    for (auto& list: substitutionList) {
        for (auto& subst: list) {
            delete subst;
        }
    }
    for (auto& list: hashCon) {
        delete list.second;
    }
}

string SimpleADTSolver::PrettyPrint(const Term* t, unsigned cpyIdx,
                                    unordered_map<variableIdentifier, string>* prettyNames) const {
    if (t->FuncID < 0) {
        if (prettyNames == nullptr)
            return "var " + VarNames[-t->FuncID - 1];
        string name;
        if (tryGetValue(*prettyNames, variableIdentifier(t->getSolverId(), t->FuncID, cpyIdx), name))
            return name;
        prettyNames->insert(make_pair(variableIdentifier(t->getSolverId(), t->FuncID, cpyIdx),
                                             name = "$" + to_string(prettyNames->size())));
        return name;
    }

    if (t->Args.empty())
        return FuncNames[t->FuncID];
    std::stringstream sb;
    sb << FuncNames[t->FuncID];
    sb << '(' << PrettyPrint(t->Args[0], cpyIdx, prettyNames);
    for (int i = 1; i <t->Args.size(); i++) {
        sb << ',' << PrettyPrint(t->Args[i], cpyIdx, prettyNames);
    }
    sb << ')';
    return sb.str();
}

void SimpleADTSolver::EnsureFounded() {
    // Only required for Z3 expressions
    if (any_of(Domains.cbegin(), Domains.cend(), [](const std::vector<unsigned>& o) { return o.empty(); }))
        return;
    string name = "a_" + ComplexSolver.GetSolverName(SolverId);
    int idx = 1;
    if (contains_key(nameToId, name)) {
        PeekTerm(name, 0);
        return;
    }
    while (contains_key(nameToId, name = "a_" + ComplexSolver.GetSolverName(SolverId) + to_string(idx++))) {}
    PeekTerm(name, 0);
}

bool SimpleADTSolver::GetSubstitution(int id, unsigned cpy, substitution*& t) {
    t = nullptr;
    if (id >= 0)
        return false;
    auto& list = substitutionList[-id - 1];
    if (cpy >= list.size())
        return false;
    t = list[cpy];
    return t != nullptr;
}

bool SimpleADTSolver::SetSubstitution(int id, unsigned cpy, const Term* subst, unsigned substCpy, vector<literal>& just, bool probe) {
    assert(substitutionList[-id - 1].size() <= cpy || substitutionList[-id - 1][cpy] == nullptr);
    auto& prevList = substitutionList[-id - 1];
    if (prevList.size() <= cpy) {
        for (unsigned i = prevList.size(); i <= cpy; i++) {
            prevList.push_back(nullptr);
        }
    }
    prevList[cpy] = new substitution(subst, substCpy, just);
    propagator().add_undo([this, id, cpy]() {
        delete substitutionList[-id - 1][cpy];
        substitutionList[-id - 1][cpy] = nullptr;
    });

    if (!CheckCycle(subst, substCpy, id, cpy, just))
        return false;

    if (cpy >= observerList[-id - 1].size())
        return true;

    for (unsigned observed: observerList[-id - 1][cpy]) {
        LazyDiseq* diseqInfo = diseqList[observed];
        if (diseqInfo->Solved)
            continue;
        bool found = false;
        assert(!ComplexSolver.SATSplit ||
               diseqInfo->SubDisequalities.size() - diseqInfo->IrrelevantDisequalitiesCnt == 1);
        vector<observerItem> observerUpdates;
        auto subDiseq = diseqInfo->SubDisequalities;
        for (unsigned i = diseqInfo->IrrelevantDisequalitiesCnt; i < subDiseq.size(); i++) {
            auto diseq = subDiseq[i];
            // TODO: We only have to check LHS as we only monitor them?
            if ((diseq.lhs->FuncID != id || diseq.lhsCpy != cpy) &&
                (diseq.rhs->FuncID != id || diseq.rhsCpy != cpy))
                continue;
            diseq.processed = true;
            found = true;
            unsigned swpIdx = diseqInfo->IrrelevantDisequalitiesCnt;
            diseqInfo->IrrelevantDisequalitiesCnt++;
            swap(subDiseq[i], subDiseq[swpIdx]);
            propagator().add_undo([swpIdx, i, diseqInfo]() {
                diseqInfo->IrrelevantDisequalitiesCnt--;
                auto& subDiseq = diseqInfo->SubDisequalities;
                swap(subDiseq[i], subDiseq[swpIdx]);
                assert(diseqInfo->IrrelevantDisequalitiesCnt == swpIdx);
                assert(subDiseq[i].processed);
                subDiseq[i].processed = false;
            });
            vector<LazySubDiseq> diseqExt;
            vector<literal> justificationsExt;

            if (NonUnify(true,
                         diseq.lhs, diseq.lhsCpy,
                         diseq.rhs, diseq.rhsCpy,
                         justificationsExt, diseqExt, observerUpdates)) {
                diseqInfo->Solved = true;
                propagator().add_undo([diseqInfo]() { diseqInfo->Solved = false; });
                break;
            }
            unsigned prevDiseqSize = diseqInfo->SubDisequalities.size();
            unsigned prevJustSize = diseqInfo->Justifications.size();
            add_range(diseqInfo->SubDisequalities, diseqExt);
            add_range(diseqInfo->Justifications, justificationsExt);
            propagator().add_undo([diseqInfo, prevDiseqSize, prevJustSize]() {
                diseqInfo->SubDisequalities.resize(prevDiseqSize);
                diseqInfo->Justifications.resize(prevJustSize);
            });
        }

        assert(found);
        if (diseqInfo->Solved)
            continue;
#ifdef DEBUG
        for (unsigned i = 0; i < diseqInfo->IrrelevantDisequalitiesCnt; i++) {
            assert(subDiseq[i].processed);
        }
#endif
        if (diseqInfo->SubDisequalities.size() == diseqInfo->IrrelevantDisequalitiesCnt) {
            assert(observerUpdates.empty());
            if (!probe)
                propagator().propagate_conflict(diseqInfo->Justifications);
            return false;
        }

        if (ComplexSolver.SATSplit) {
            vector<formula> propagation;
            for (unsigned i = diseqInfo->IrrelevantDisequalitiesCnt; i < diseqInfo->SubDisequalities.size(); i++) {
                propagation.push_back(
                        ComplexSolver.MakeDisEqualityExpr(
                                diseqInfo->SubDisequalities[i].lhs, diseqInfo->SubDisequalities[i].lhsCpy,
                                diseqInfo->SubDisequalities[i].rhs, diseqInfo->SubDisequalities[i].rhsCpy));
            }
            propagator().propagate(diseqInfo->Justifications, propagator().m.mk_or(propagation));
            continue;
        }

        for (const observerItem& observer: observerUpdates) {
            for (unsigned i = observerList[observer.idx].size(); i <= observer.cpy; i++) {
                observerList[observer.idx].emplace_back();
            }
            if (!observerList[observer.idx][observer.cpy].insert(observed).second)
                continue;
            propagator().add_undo(
                    [this, observer, observed]() { observerList[observer.idx][observer.cpy].erase(observed); });
        }
    }
    return true;
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

Term* SimpleADTSolver::MakeTerm(int id, const pvector<Term>& args) {
    assert(id >= 0);
    if (id >= FuncNames.size())
        throw solving_exception("Term index out of bounds");
    return MakeTermInternal(id, args);
}

Term* SimpleADTSolver::MakeTermInternal(int id, const pvector<Term>& args) {
    const RawTermWrapper key(new RawTerm(id, args));
    Term* t = nullptr;
    if (tryGetValue(hashCon, key, t)) {
        delete key.obj;
        return t;
    }
    delete key.obj;
    t = new Term(id, args, *this, hashCon.size());
    hashCon.insert(make_pair(RawTermWrapper(t), t));
    return t;
}

Term* SimpleADTSolver::MakeVar(const string& name) {
    int id = 0;
    if (!tryGetValue(nameToId, name, id)) {
        id = -((int) VarNames.size() + 1);
        substitutionList.emplace_back();
        VarNames.push_back(name);
        observerList.emplace_back();
        nameToId.insert(make_pair(name, id));
    }
    if (id >= 0)
        throw solving_exception("Name already used by function");
    return MakeVar(-id - 1);
}

Term* SimpleADTSolver::MakeVar(int idx) {
    if (idx >= VarNames.size())
        throw solving_exception("Variable index out of bounds");
    return MakeTermInternal(-(idx + 1), {});
}

bool SimpleADTSolver::Unify(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy, vector<literal>& justifications) {

    if (lhs->HashID == rhs->HashID && (lhsCpy == rhsCpy || lhs->Ground))
        return true;
    if (lhs->Ground && rhs->Ground && lhs->HashID != rhs->HashID) {
        propagator().propagate_conflict(justifications);
        return false;
    }

    substitution* subst1 = nullptr;
    substitution* subst2 = nullptr;
    if (GetSubstitution(lhs->FuncID, lhsCpy, subst1)) {
        unsigned prev = justifications.size();
        add_range(justifications, subst1->just);
        if (!Unify(subst1->subst, subst1->cpy, rhs, rhsCpy, justifications))
            return false;
        justifications.resize(prev);
        return true;
    }
    if (GetSubstitution(rhs->FuncID, rhsCpy, subst2)) {
        unsigned prev = justifications.size();
        add_range(justifications, subst2->just);
        if (!Unify(lhs, lhsCpy, subst2->subst, subst2->cpy, justifications))
            return false;
        justifications.resize(prev);
        return true;
    }

    if (lhs->FuncID >= 0 && rhs->FuncID >= 0 && lhs->FuncID != rhs->FuncID) {
        propagator().propagate_conflict(justifications);
        return false;
    }

    if (lhs->FuncID == rhs->FuncID && lhs->FuncID >= 0) {
        for (int i = 0; i < lhs->Args.size(); i++) {
            if (!Unify(lhs->Args[i], lhsCpy, rhs->Args[i], rhsCpy, justifications))
                return false;
        }
        return true;
    }

    if (rhs->FuncID < 0) {
        swap(lhs, rhs);
        swap(lhsCpy, rhsCpy);
    }
    assert(lhs->FuncID < 0);

    return SetSubstitution(lhs->FuncID, lhsCpy, rhs, rhsCpy, justifications, false);
}

bool SimpleADTSolver::CheckCycle(const RawTerm* t, unsigned cpy, int assignmentId, unsigned assignmentCpyId,
                                 vector<literal>& justifications) {
    if (t->FuncID >= 0) {
        for (auto* arg: t->Args) {
            if (!CheckCycle((RawTerm*) arg, cpy, assignmentId, assignmentCpyId, justifications))
                return false;
        }
        return false;
    }

    if (t->FuncID == assignmentId && cpy == assignmentCpyId) {
        // Found the cycle
        propagator().propagate_conflict(justifications);
        return false;
    }

    substitution* subst = nullptr;
    if (!GetSubstitution(t->FuncID, cpy, subst))
        return true;

    for (auto* j: subst->just) {
        // TODO: Improve this
        justifications.push_back(j);
    }
    if (!CheckCycle(subst->subst, subst->cpy, assignmentId, assignmentCpyId, justifications))
        return false;
    justifications.pop_back();
    return true;
}

bool SimpleADTSolver::AreEqual(const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
    if (lhs->HashID == rhs->HashID && (lhsCpy == rhsCpy || lhs->Ground))
        return true;
    if (lhs->Ground && rhs->Ground && lhs->HashID != rhs->HashID)
        return false;

    substitution* subst1 = nullptr;
    substitution* subst2 = nullptr;
    if (GetSubstitution(lhs->FuncID, lhsCpy, subst1))
        return AreEqual(subst1->subst, subst1->cpy, rhs, rhsCpy);
    if (GetSubstitution(rhs->FuncID, rhsCpy, subst2))
        return AreEqual(lhs, lhsCpy, subst2->subst, subst2->cpy);

    if (lhs->FuncID < 0 || rhs->FuncID < 0 || lhs->FuncID != rhs->FuncID)
        return false;

    for (int i = 0; i < lhs->Args.size(); i++) {
        if (!AreEqual(lhs->Args[i], lhsCpy, rhs->Args[i], rhsCpy))
            return false;
    }
    return true;
}

bool SimpleADTSolver::NonUnify(literal just, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy) {
    auto* lazyDiseq = new LazyDiseq();
    lazyDiseq->Justifications.push_back(just);
    vector<observerItem> observerUpdates;

    if (NonUnify(false, lhs, lhsCpy, rhs, rhsCpy, lazyDiseq->Justifications, lazyDiseq->SubDisequalities,
                 observerUpdates))
        return true;
    if (lazyDiseq->SubDisequalities.empty()) {
        propagator().propagate_conflict(lazyDiseq->Justifications);
        return false;
    }
    if (ComplexSolver.SATSplit) {
        LazySubDiseq diseq;

        if (lazyDiseq->SubDisequalities.size() > 1 ||
            *(diseq = lazyDiseq->SubDisequalities[0]).lhs == *lhs && diseq.lhsCpy == lhsCpy &&
            *diseq.rhs == *rhs && diseq.rhsCpy == rhsCpy) {
            // Either there is a split (> 1 cases) or there the disequality
            // can be simplified => Propagate back to Z3
            vector<formula> propagation;
            for (auto& subDiseq: lazyDiseq->SubDisequalities) {
                propagation.push_back(
                        ComplexSolver.MakeDisEqualityExpr(subDiseq.lhs, subDiseq.lhsCpy,
                                                          subDiseq.rhs, subDiseq.rhsCpy));
            }
            propagator().propagate(lazyDiseq->Justifications, propagator().m.mk_or(propagation));
            return true;
        }
        // Otherwise add to watchlist as usual...
    }
    unsigned idx = diseqList.size();
    for (observerItem& observer: observerUpdates) {

        for (unsigned i = observerList[observer.idx].size(); i <= observer.cpy; i++) {
            observerList[observer.idx].emplace_back();
        }

        if (!observerList[observer.idx][observer.cpy].insert(idx).second)
            continue;
        propagator().add_undo([this, observer, idx]() { observerList[observer.idx][observer.cpy].erase(idx); });
    }
    diseqList.push_back(lazyDiseq);
    propagator().add_undo([this]() { diseqList.pop_back(); });
    return false;
}

bool SimpleADTSolver::NonUnify(bool skipRoot, const Term* lhs, unsigned lhsCpy, const Term* rhs, unsigned rhsCpy,
                               vector<literal>& justifications, vector<LazySubDiseq>& delayed,
                               vector<observerItem>& observerUpdates) {

    if (lhs->HashID == rhs->HashID && (lhsCpy == rhsCpy || lhs->Ground))
        return false;
    if (lhs->Ground && rhs->Ground && lhs->HashID != rhs->HashID)
        return true;
    substitution* subst1 = nullptr;
    substitution* subst2 = nullptr;
    if (GetSubstitution(lhs->FuncID, lhsCpy, subst1)) {
        add_range(justifications, subst1->just);
        auto res = NonUnify(false, subst1->subst, subst1->cpy, rhs, rhsCpy,
                            justifications, delayed, observerUpdates);
        return res;
    }
    if (GetSubstitution(rhs->FuncID, rhsCpy, subst2)) {
        add_range(justifications, subst2->just);
        auto res = NonUnify(false, lhs, lhsCpy, subst2->subst, subst2->cpy,
                            justifications, delayed, observerUpdates);
        return res;
    }
    if (lhs->FuncID >= 0 && rhs->FuncID >= 0) {
        if (lhs->FuncID != rhs->FuncID)
            return true;
        for (int i = 0; i < lhs->Args.size(); i++) {
            if (NonUnify(false, lhs->Args[i], lhsCpy, rhs->Args[i], rhsCpy,
                         justifications, delayed, observerUpdates))
                return true;
        }
        return false;
    }
    if (rhs->FuncID < 0) {
        swap(lhs, rhs);
        swap(lhsCpy, rhsCpy);
    }
    assert(lhs->FuncID < 0);

    if (!skipRoot) {
        delayed.emplace_back(lhs, lhsCpy, rhs, rhsCpy);
        observerUpdates.emplace_back(-lhs->FuncID - 1, lhsCpy);
        // We don't need this:
        // if (rhs.FuncID < 0)
        //    observerUpdates.push_back((-rhs.FuncID - 1, rhsCpy));
    }
    return false;
}

string SimpleADTSolver::ToString() const {
    stringstream sb;
    for (int i = 0; i < FuncNames.size(); i++) {
        sb << FuncNames[i] << '/' << to_string(Domains[i].size());
    }
    return sb.str();
}

optional<term_instance> SimpleADTSolver::GetModel(int varId, unsigned copyIdx) const {
    int idx = -varId - 1;
    if (substitutionList[idx].size() <= copyIdx)
        return nullopt;
    if (substitutionList[idx][copyIdx] == nullptr)
        return nullopt;
    return make_optional(term_instance(substitutionList[idx][copyIdx]->subst, substitutionList[idx][copyIdx]->cpy));
}

string SimpleADTSolver::GetModel() {
    stringstream sb;
    unordered_map<variableIdentifier, string> prettyNames;
    for (int v = 0; v < substitutionList.size(); v++) {
        auto subst = substitutionList[v];
        for (auto cpy = 0; cpy < subst.size(); cpy++) {
            auto* subst2 = subst[cpy];
            if (subst2 == nullptr)
                continue;
            sb << "(= " <<
               PrettyPrint(MakeVar(-v - 1), cpy, &prettyNames) << ' ' <<
               PrettyPrint(subst2->subst, subst2->cpy, &prettyNames) << ")\n";
        }
    }
    return sb.str();
}
