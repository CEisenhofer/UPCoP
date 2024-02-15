#include "PropagatorBase.h"
#include <iostream>

unsigned PropagatorBase::getRandom(unsigned min, unsigned max) const {
    assert(max > min);
    unsigned res = distribution(generator);
    unsigned span = max - min;
    return min + res % span;
}

PropagatorBase::PropagatorBase(CNF<IndexedClause*>& cnf, ComplexADTSolver& adtSolver, ProgParams& progParams, unsigned literalCnt)
    : term_solver(adtSolver), generator(0), progParams(progParams), matrix(cnf), UnificationHints(literalCnt) {

    term_solver.propagator = this;

    pvector<IndexedClause> posClauses;
    pvector<IndexedClause> negClauses;
    posClauses.reserve(cnf.size());
    negClauses.reserve(cnf.size());

    for (unsigned i = 0; i < cnf.size(); i++) {
        auto* clause = cnf[i];
        if (cnf.IsConjecture(i))
            initClauses.push_back(clause);
        bool allPos = true;
        bool allNeg = true;
        for (const auto& lit: clause->literals) {
            if (allPos && !lit->polarity)
                allPos = false;
            if (allNeg && lit->polarity)
                allNeg = false;
            if (!allPos && !allNeg)
                break;
        }
        assert(!allPos || !allNeg);
        if (allPos)
            posClauses.push_back(clause);
        else if (allNeg)
            negClauses.push_back(clause);
    }
    if (posClauses.empty() || negClauses.empty()) {
        Satisfiable = true;
        return;
    }

    auto smallestClauseSet = posClauses.size() < negClauses.size() ? posClauses : negClauses;

    if (progParams.Conjectures == Auto)
        progParams.Conjectures =
                initClauses.size() > 1 &&
                (unsigned) log2((double)initClauses.size()) > smallestClauseSet.size() ? Min : Keep;
    if (initClauses.empty() && progParams.Conjectures == Keep)
        progParams.Conjectures = Min;

    assert(progParams.Conjectures != Auto);

    if (progParams.Conjectures == Pos)
        initClauses = posClauses;
    else if (progParams.Conjectures == Neg)
        initClauses = negClauses;
    else if (progParams.Conjectures == Min)
        initClauses = smallestClauseSet;
    else {
        assert(progParams.Conjectures == Keep);
    }

    assert(!initClauses.empty());
}

Large2DArray::Large2DArray(unsigned size) : size(size) {
    if (size < (1 << 14)) {
        small = make_optional(pvector<const SubtermHint>());
        small->resize((size_t)size * size);
        large = nullopt;
    } else {
        small = nullopt;
        large = make_optional(unordered_map<pair<unsigned, unsigned>, const SubtermHint*>(14591 /* some large prime */));
    }
}

Large2DArray::~Large2DArray() {
    if (small.has_value()) {
        for (const SubtermHint* r: small.value()) {
            if (r != nullptr && !is_invalid(r))
                delete r;
        }
    } else {
        for (auto r: large.value()) {
            if (r.second != nullptr && !is_invalid(r.second))
                delete r.second;
        }
    }
}

const SubtermHint* Large2DArray::get(unsigned i, unsigned j) const {
    if (small.has_value())
        return (*small)[i * size + j];
    const SubtermHint* res;
    if (tryGetValue(*large, make_pair(i, j), res))
        return res;
    return nullptr;
}

void Large2DArray::set(unsigned i, unsigned j, const SubtermHint* hint) {
    if (small.has_value()) {
        assert((*small)[i * size + j] == nullptr);
        (*small)[i * size + j] = hint;
        return;
    }
    assert(large->find(make_pair(i, j)) == large->end());
    large->insert(make_pair(make_pair(i, j), hint));
}

void SubtermHint::GetPosConstraints(PropagatorBase& propagator, const GroundLiteral& l1, const GroundLiteral& l2, vector<formula>& constraints) const {
    auto [lhsCpy, rhsCpy] = GetCpyIdx(l1, l2);
    for (auto [lhs, rhs]: equalities) {
        formula e = propagator.term_solver.MakeEqualityExpr(lhs, lhsCpy, rhs, rhsCpy);
        if (e->is_false()) {
            constraints.resize(0);
            constraints.push_back(propagator.m.mk_false());
            return;
        }
        if (e->is_true())
            continue;
        constraints.push_back(e);
    }
}

formula SubtermHint::GetNegConstraints(PropagatorBase& propagator, const GroundLiteral& l1, const GroundLiteral& l2) const {
    auto [lhsCpy, rhsCpy] = GetCpyIdx(l1, l2);
    pvector<formula_term> orList;
    for (const auto& [lhs, rhs] : equalities) {
        formula e = propagator.term_solver.MakeEqualityExpr(lhs, lhsCpy, rhs, rhsCpy);
        if (e->is_false())
            return propagator.m.mk_true();
        if (e->is_true())
            continue;
        orList.push_back(propagator.m.mk_not(e));
    }
    return propagator.m.mk_or(orList);
}

bool SubtermHint::IsSatisfied(const GroundLiteral& l1, const GroundLiteral& l2) const {
    auto [lhsCpy, rhsCpy] = GetCpyIdx(l1, l2);
    for (const auto& [lhs, rhs]: equalities) {
        if (!ComplexADTSolver::AreEqual(lhs, lhsCpy, rhs, rhsCpy))
            return false;
    }
    return true;
}

SubtermHint* PropagatorBase::CollectConstrainUnifiable(const GroundLiteral& l1, const IndexedLiteral& l2) const {
    // l1 has to be ground; otw. P(:auto 0) [l1] and P(:auto 0) [l2] would say that they are always equal
    auto* hint = new SubtermHint();
    unsigned arity = l1.GetArity();

    for (unsigned i = 0; i < arity; i++) {
        Term* lhs = l1.Literal->ArgBases[i];
        Term* rhs = l2.ArgBases[i];
        if (!lhs->SeemsPossiblyUnifiable(rhs, *hint)) {
            delete hint;
            return nullptr;
        }
    }
    return hint;
}

void PropagatorBase::CacheUnification(const GroundLiteral& l1, const IndexedLiteral& l2) {
    if (UnificationHints.get(l1.Literal->Index, l2.Index) != nullptr)
        return;
    SubtermHint* hint;
    if (l1.Literal->nameID == l2.nameID &&
        (hint = CollectConstrainUnifiable(l1, l2)) != nullptr) {

        UnificationHints.set(l1.Literal->Index, l2.Index, hint);
        if (l2.Index != l1.Literal->Index)
            UnificationHints.set(l2.Index, l1.Literal->Index, hint->swap());
    }
    else {
        UnificationHints.set_invalid(l1.Literal->Index, l2.Index);
        if (l2.Index != l1.Literal->Index)
            UnificationHints.set_invalid(l2.Index, l1.Literal->Index);
    }
}

void PropagatorBase::CreateTautologyConstraints(IndexedClause& clause) {
    /*
    clause.TautologyConstraints.emplace();
    auto ground = GetRootGround(clause);

    for (int k = 0; k < clause.size(); k++) {
        for (int l = k + 1; l < clause.size(); l++) {
            if (
                    clause[k]->polarity != clause[l]->polarity &&
                    clause[k]->nameID == clause[l]->nameID) {

                auto diseq = CollectConstrainUnifiable(ground[k], clause[l]);
                if (diseq == nullptr)
                    continue;
                // Clause contains two complementary literals
                // Why did the simplifier not remove those?!
                assert(!diseq->tautology());
                clause.TautologyConstraints->emplace_back(k, l, diseq);
            }
        }
    }*/
}

void PropagatorBase::fixed(literal var, bool value) {
    if (is_conflict)
        return;
    try {
        if (term_solver.Asserted(var, value))
            return;

        fixed2(var, value);
    }
    catch (...) {
        cout << "Crashed" << endl;
        exit(131);
    }
}

string PropagatorBase::ClauseToString(const vector<GroundLiteral>& ground,
                                        unordered_map<variableIdentifier, string>* prettyNames) {
    if (ground.empty())
        return "false";
    if (ground.size() == 1)
        return PrettyPrintLiteral(ground[0], prettyNames);
    stringstream sb;
    sb << '(' << PrettyPrintLiteral(ground[0], prettyNames);
    for (int i = 1; i < ground.size(); i++) {
        sb << " || " << PrettyPrintLiteral(ground[i], prettyNames);
    }
    sb << ')';
    return sb.str();
}

string PropagatorBase::PrettyPrintLiteral(const Literal* l, unsigned cpyIdx,
                                            unordered_map<variableIdentifier, string>* prettyNames) {
    stringstream sb;
    if (!l->polarity)
        sb << "not ";
    sb << l->name;
    if (l->Arity() == 0)
        return sb.str();
    sb << '(';
    sb << l->ArgBases[0]->PrettyPrint(cpyIdx, prettyNames);
    for (int i = 1; i < l->Arity(); i++) {
        sb << ", " << l->ArgBases[i]->PrettyPrint(cpyIdx, prettyNames);
    }
    sb << ')';
    return sb.str();
}