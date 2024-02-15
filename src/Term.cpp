#include "PropagatorBase.h"

size_t hash<RawTerm>::operator()(const RawTerm& x) const {
    static const hash<Term> hash;
    size_t ret = x.FuncID;
    for (auto* arg : x.Args)
        ret = 31 * ret + hash(*arg);
    return ret;
}

size_t hash<Term>::operator()(const Term& x) const {
    return 233 * x.getSolverId() + x.HashID;
}

size_t std::hash<variableIdentifier>::operator()(const variableIdentifier& x) const {
    return 233 * x.solverId + x.id + x.cpyIdx;
}

size_t std::hash<term_instance>::operator()(const term_instance& x) const {
    static const hash<Term> hash;
    return hash(*x.term) * 133 + x.cpyIdx;
}

unsigned Term::getSolverId() const { return Solver.SolverId; }

Term::Term(int funcId, pvector<Term> args, SimpleADTSolver& solver, unsigned hashId) :
        RawTerm(funcId, std::move(args)), HashID(hashId), Solver(solver),
        Ground(funcId >= 0 && all_of(Args.cbegin(), Args.cend(), [](Term* o) { return o->Ground; })) {
}

bool Term::SeemsPossiblyUnifiable(Term* rhs, SubtermHint& hint) {
    if (FuncID < 0 || rhs->FuncID < 0) {
        hint.add(this, rhs);
        return true;
    }
    if (HashID == rhs->HashID && Ground) {
        assert(rhs->Ground);
        return true;
    }
    if (FuncID < 0 || rhs->FuncID < 0) {
        hint.add(this, rhs);
        return true;
    }
    if (FuncID != rhs->FuncID)
        return false;

    assert(Args.size() == rhs->Args.size());

    for (int i = 0; i < Args.size(); i++) {
        if (!Args[i]->SeemsPossiblyUnifiable(rhs->Args[i], hint))
            return false;
    }
    return true;
}

string Term::to_string() const {
    return Solver.PrettyPrint(this, 0, nullptr);
}

string Term::PrettyPrint(unsigned cpyIdx, unordered_map<variableIdentifier, string>* prettyNames) const {
    return Solver.PrettyPrint(this, cpyIdx, prettyNames);
}
