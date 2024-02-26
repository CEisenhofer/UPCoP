#include <utility>

#include "propagator_base.h"

size_t hash<raw_term>::operator()(const raw_term& x) const {
    static const hash<term> hash;
    size_t ret = x.FuncID;
    for (auto* arg: x.Args)
        ret = 31 * ret + hash(*arg);
    return ret;
}

size_t hash<term>::operator()(const term& x) const {
    return 233 * x.getSolverId() + x.HashID;
}

size_t std::hash<term_instance>::operator()(const term_instance& x) const {
    static const hash<term> hash;
    return hash(*x.t) * 133 + x.cpyIdx;
}

void EqualityJustification::AddJustification(SimpleADTSolver* adtSolver, vector<literal>& just) {
    vector<Justification*> justifications;
    adtSolver->FindJust(LHS, RHS, justifications);
    for (auto* j: justifications) {
        assert(j);
        j->AddJustification(adtSolver, just);
    }
}

string EqualityJustification::to_string() const {
    return LHS->to_string() + " == " + RHS->to_string();
}

string CheckPosition::to_string() const {
    return LHS->to_string() + "[" + std::to_string(ArgIdx) + "]  <> " + RHS->to_string() + "[" + std::to_string(ArgIdx);
}

lessThan::lessThan(term_instance* lhs, term_instance* rhs) : LHS(lhs), RHS(rhs) {
}

string lessThan::to_string() const {
    return LHS->to_string() + " < " + RHS->to_string();
}

equality::equality(term_instance* lhs, term_instance* rhs, vector<Justification*> just) : just(std::move(just)) {
    if (lhs->compare_to(rhs) <= 0) {
        LHS = lhs;
        RHS = rhs;
    }
    else {
        LHS = rhs;
        RHS = lhs;
    }
}

string equality::to_string() const {
    return LHS->to_string() + " == " + RHS->to_string();
}

size_t hash<equality>::operator()(const equality& x) const {
    size_t h = (size_t) x.LHS;
    h ^= (size_t) x.RHS + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

size_t hash<lessThan>::operator()(const lessThan& x) const {
    size_t h = (size_t) x.LHS;
    h ^= (size_t) x.RHS + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

term_instance* term_instance::FindRootQuick(propagator_base& propagator) {
    term_instance* current = this;
    while (current != current->parent) {
        current = current->parent;
    }
    if (current == parent)
        return current;

    auto* prev = parent;
    propagator.add_undo([this, prev]() { parent = prev; });
    parent = current;
    return current;
}

unsigned term::getSolverId() const { return Solver.SolverId; }

term::term(int funcId, pvector<term> args, SimpleADTSolver& solver, unsigned hashId) :
        raw_term(funcId, std::move(args)), HashID(hashId), Solver(solver),
        Ground(funcId >= 0 && all_of(Args.cbegin(), Args.cend(), [](term* o) { return o->Ground; })) {
}

term::~term() {
    reset();
}

void term::reset() {
    for (term_instance* inst : instances)
        delete inst;
    instances.clear();
}

term_instance* term::GetInstance(unsigned cpy) const {
    for (unsigned i = instances.size(); i <= cpy; i++) {
        instances.push_back(term_instance::NewInstance(this, i));
    }
    return instances[cpy];
}

bool term::SeemsPossiblyUnifiable(term* rhs, subterm_hint& hint) {
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

string term::to_string() const {
    return Solver.PrettyPrint(this, 0, nullptr);
}

string term::PrettyPrint(unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const {
    return Solver.PrettyPrint(this, cpyIdx, prettyNames);
}
