#include "propagator_base.h"
#include <iostream>
#include <chrono>

#ifndef NDEBUG
std::unordered_map<unsigned, std::string> names;
#endif

#ifndef NDEBUG
void CaDiCal_propagator::output_literals(const std::vector<literal>& lit) const {
    std::vector<literal> unassigned;
    std::vector<literal> wrong_val;
    std::unordered_set<literal> seen;
    for (unsigned i = 0; i < lit.size(); i++) {
        literal j = lit[i];
        if (seen.find(j) != seen.end())
            continue;
        bool val = false;
        if (!j->is_true()) {
            if (!get_value(j, val)) {
                unassigned.push_back(j);
            }
            else if (val != (j->get_lit() > 0)) {
                wrong_val.push_back(j);
            }
            Log(j->to_string());
        }
        else {
            Log("[" << j->to_string() << "]");
        }
        seen.insert(j);
        if (i + 1 < lit.size())
            Log(", ");
    }
    if (!wrong_val.empty()) {
        LogN("");
        for (const auto* j : wrong_val) {
            LogN("Inconsistent interpretation: " << j->to_string() << " is not " << (j->get_lit() > 0));
        }
    }
    if (!unassigned.empty()) {
        LogN("");
        for (const auto* j : unassigned) {
            LogN("\nUnassigned: " << j->to_string());
        }
    }
    if (!(wrong_val.empty() && unassigned.empty())){
        assert(false);
    }
}
#endif

static unsigned incCnt = 0;

void CaDiCal_propagator::propagate_conflict(const justification& just) {
    assert(just.diseqJust.first == nullptr && just.diseqJust.second == nullptr);
    if (base->is_conflict())
        return;
    // assert(just.size() > 1); // No general problem with that, but this looks suspicious...
    base->set_conflict();
    vector<literal> lits;
    just.resolve_justification(*base, lits);
#ifndef NDEBUG
    Log("conflict (hard) [" << incCnt++ << "]: ");
    output_literals(lits);
    LogN("");
#endif

    std::vector<int> aux;
    aux.reserve(lits.size());
    for (literal k : lits) {
        if (k->is_true())
            continue;
        aux.push_back(-k->get_lit());
    }

#ifdef DIMACS
    for (int l: aux) {
        dimacs << l << " ";
    }
    dimacs << "0\n";
#endif

    pending_hard_propagations.emplace_back(std::move(aux));
}

bool CaDiCal_propagator::hard_propagate(const justification& just, formula prop) {
    assert(just.diseqJust.first == nullptr && just.diseqJust.second == nullptr);
    if (base->is_conflict())
        return false;
    if (prop->is_true())
        return true;
    if (prop->is_false()) {
        propagate_conflict(just);
        return false;
    }

    vector<literal> lits;
    just.resolve_justification(*base, lits);

#ifndef NDEBUG
    Log("Propagating (hard) [" << incCnt++ << "]: ");
    output_literals(lits);
    Log(" => ");
    LogN(prop->to_string());
#endif

    std::vector<std::vector<int>> aux;
    const literal_term* c = prop->get_lits(*base, aux);
    aux.emplace_back();
    aux.back().reserve(lits.size());
    aux.back().push_back(c->get_lit());
    for (literal k : lits) {
        if (k->is_true())
            continue;
        aux.back().push_back(-k->get_lit());
    }
    // aux.back().second = prop; -- not required; the get_lits should do that

    if (contains(prev_propagations, aux.back())) {
        assert(aux.size() == 1);
        // We already propagated this -> skip
        return true;
    }
    for (auto& k: aux) {
#ifdef DIMACS
        for (int l: k) {
            dimacs << l << " ";
        }
        dimacs << "0\n";
#endif
        pending_hard_propagations.emplace_back(std::move(k));
    }
    prev_propagations.insert(aux.back());

#ifdef PUSH_POP
    std::vector<int> aux2 = std::move(aux.back());
    undo_stack.emplace_back([this, aux2]() {
        prev_propagations.erase(aux2);
    });
#endif
    // std::cout << "Propagation cnt: " << pending_hard_propagations.size() << " current idx: " << pending_hard_propagations_idx << std::endl;
    return true;
}

bool CaDiCal_propagator::soft_propagate(const justification& just, literal prop) {
    assert(just.diseqJust.first == nullptr && just.diseqJust.second == nullptr);
    if (base->is_conflict())
        return false;
    if (prop->is_true())
        return true;
    if (prop->is_false()) {
        propagate_conflict(just);
        return false;
    }
    if (!soft_justifications[literal_to_idx(prop->get_lit())].empty())
        // Already propagated
        return true;

    bool val = false;
    if (get_value(prop, val)) {
        if ((prop->get_lit() > 0) == val)
            // Already assigned
            return true;
        justification just2 = just;
        just2.push_literal(m.mk_not(prop));
        propagate_conflict(just2);
        return false;
    }

    vector<literal> lits;
    just.resolve_justification(*base, lits);

#ifndef NDEBUG
    Log("Propagating (soft) [" << incCnt++ << "]: ");
    output_literals(lits);
    Log(" => ");
    LogN(prop->to_string() << " [" << prop->get_lit() << "]");
#endif

    std::vector<int> j;
    j.reserve(lits.size() + 1);
    for (literal k : lits) {
        if (k->is_true())
            continue;
        j.push_back(-k->get_lit());
    }
    const int propLit = prop->get_lit();
    j.push_back(propLit);

#ifdef DIMACS
    for (int l: j) {
        dimacs << l << " ";
    }
    dimacs << "0\n";
#endif

    pending_soft_propagations.emplace_back(std::move(j), propLit);
    return true;
}

CaDiCal_propagator::CaDiCal_propagator(propagator_base* base, unsigned timeLeft) : base(base), m(base), solver(new CaDiCaL::Solver()),
                                                            stopTime(std::chrono::milliseconds(timeLeft) + std::chrono::high_resolution_clock::now()) {
    solver->set("ilb", 0);
    solver->set("ilbassumptions", 0);
    // solver->set("chrono", 0);
    // solver->set("phase", 0);
    solver->set("inprocessing", 0);
    solver->set("lucky", 0);
    solver->set("walk", 0);
    solver->configure("plain");
    solver->connect_terminator(this);
    solver->connect_fixed_listener(this);
    solver->connect_external_propagator(this);
    // are_reasons_forgettable = true;
#ifndef NDEBUG
    reset_names();
#endif
}

CaDiCal_propagator::~CaDiCal_propagator() {
    delete solver;
}

static unsigned fixedCnt = 0;

void CaDiCal_propagator::notify_assignment(const vector<int>& lits) {
    for (int lit : lits) {
        if (base->is_conflict())
            return;
        bool value = lit > 0;

        const unsigned id = abs(lit);
        fixedCnt++;
        literal v = m.mk_lit(id);
        LogN("Fixed [" << fixedCnt << "]: " << v->to_string() << " := " << value << " [" << lit << "]");
        assert(hard_propagation_read_idx == 0);
        bool prevValue = false;
        if (get_value(v, prevValue)) {
            assert(prevValue == value);
            return;
        }
        interpretation[id - 1] = value ? sat : unsat;
        base->get_undo().emplace_back([this, id]() {
            interpretation[id - 1] = undef;
        });

        base->fixed(v, value);
    }
}

void CaDiCal_propagator::notify_fixed_assignment(int id) {
#ifndef NDEBUG
    assert(id != 0);
    if (interpreted[abs(id) - 1]) {
        LogN("Permanently fixed " << m.mk_lit(id)->to_string() << " [" << id << "]");
    }
#endif
    literal l = m.mk_lit(id);
    l->fix(true);
    l->negate()->fix(false);
    assert(interpretation[abs(id) - 1] == undef || interpretation[abs(id) - 1] == id > 0 ? sat : unsat);
}

void CaDiCal_propagator::notify_new_decision_level() {
    assert(hard_propagation_read_idx == 0);
    LogN("Pushed " + to_string(undo_stack_limit.size()));
    undo_stack_limit.push_back(base->get_undo().size());

    soft_propagation_limit.push_back(pending_soft_propagations.size());
    assert(pending_hard_propagations.size() == pending_hard_propagations_idx);
    assert(pending_soft_propagations.size() == soft_propagation_read_idx);
    base->push();
}

void CaDiCal_propagator::notify_backtrack(size_t new_level) {
    if (new_level >= undo_stack_limit.size()) {
        // CaDiCal went crazy - let's ignore
        assert(new_level == 0);
        assert(undo_stack_limit.empty());
        return;
    }
    assert(hard_propagation_read_idx == 0);
    LogN("Pop to " << new_level);

    base->clear_conflict();

    assert(soft_propagations_explanation_idx == 0);

    const unsigned prevPending = soft_propagation_limit[new_level];
    soft_propagation_limit.resize(new_level);

    for (unsigned i = prevPending; i < soft_propagation_read_idx; i++) {
        soft_justifications[literal_to_idx(pending_soft_propagations[i].second)].clear();
    }
    pending_soft_propagations.resize(prevPending);
    soft_propagation_read_idx = pending_soft_propagations.size();

    const unsigned prevAction = undo_stack_limit[new_level];
    undo_stack_limit.resize(new_level);
    vector<action>& undo_stack = base->get_undo();
    while (undo_stack.size() > prevAction) {
        undo_stack.back()();
        undo_stack.pop_back();
    }
}

bool CaDiCal_propagator::cb_check_found_model(const std::vector<int>& model) {
    assert(hard_propagation_read_idx == 0);
    if (soft_propagation_read_idx < pending_soft_propagations.size()) {
        // TODO: Actually, this is a "bug" in CaDiCal...
        // Either we are done or there is a conflict somewhere => look for it and hard propagate it
        std::cout << "CaDiCal missed final propagation" << std::endl;
        unsigned i = soft_propagation_read_idx;
        for (; i < pending_soft_propagations.size(); i++) {
            assert(interpretation[abs(pending_soft_propagations[i].second) - 1] != undef);
            if ((interpretation[abs(pending_soft_propagations[i].second) - 1] == sat) != pending_soft_propagations[i].second > 0)
                break;
        }
        if (i < pending_soft_propagations.size()) {
            std::cout << "Conflict found - translate it to a hard propagation" << std::endl;
            justification just(pending_soft_propagations[i].first.size());
            for (unsigned j = 0; j < pending_soft_propagations[i].first.size() - 1; j++) {
                just.push_literal(m.mk_lit(pending_soft_propagations[i].first[j]));
            }
            hard_propagate(just, m.mk_lit(pending_soft_propagations[i].first.back()));
            return false;
        }
        // Fall through
    }
    // assert(soft_propagation_read_idx == pending_soft_propagations.size());
    assert(!base->is_conflict());
    base->final();
    return pending_hard_propagations.size() == pending_hard_propagations_idx && !base->is_conflict();
}

static int invCnt = 0;

int CaDiCal_propagator::cb_propagate() {
    if (base->is_conflict())
        return 0;
    invCnt++;
    if (soft_propagation_read_idx >= pending_soft_propagations.size())
        return 0;
    auto& [just, prop] = pending_soft_propagations[soft_propagation_read_idx++];
    int ret = prop;
    const unsigned idx = literal_to_idx(ret);
    assert(!just.empty());
    assert(ret != 0);
    assert(soft_justifications[idx].empty() || interpretation[abs(ret) - 1] == (ret > 0 ? sat : unsat));
    soft_justifications[idx] = just;
#ifdef PUSH_POP
    undo_stack.emplace_back([this, idx](){ soft_justifications[idx].clear(); });
#endif
    LogN("Enforced " << ret);
    return ret;
}


static int reasCnt = 0;

int CaDiCal_propagator::cb_add_reason_clause_lit(int propagated_lit) {
    unsigned idx = literal_to_idx(propagated_lit);
    assert(!soft_justifications[idx].empty());
    if (soft_propagations_explanation_idx == 0) {
        reasCnt++;
        Log("Reason [" << reasCnt << "] for " << propagated_lit << ":");
    }
    if (soft_propagations_explanation_idx < soft_justifications[idx].size()) {
        Log(" " << soft_justifications[idx][soft_propagations_explanation_idx]);
        return soft_justifications[idx][soft_propagations_explanation_idx++];
    }
    LogN("");
    soft_propagations_explanation_idx = 0;
    return 0;
}


bool CaDiCal_propagator::cb_has_external_clause(bool& is_forgettable) {
#ifdef PUSH_POP
    is_forgettable = true;
    are_reasons_forgettable = true;
#endif
    return pending_hard_propagations_idx < pending_hard_propagations.size();
}

int CaDiCal_propagator::cb_add_external_clause_lit() {
#ifndef NDEBUG
    bool f = false;
    assert(cb_has_external_clause(f));
#endif
    auto& toAdd = pending_hard_propagations[pending_hard_propagations_idx];
    if (hard_propagation_read_idx >= toAdd.size()) {
        pending_hard_propagations_idx++;
        hard_propagation_read_idx = 0;

        if (pending_hard_propagations_idx >= pending_hard_propagations.size()) {
            pending_hard_propagations.clear();
            pending_hard_propagations_idx = 0;
        }
        return 0;
    }
    return toAdd[hard_propagation_read_idx++];
}

int CaDiCal_propagator::cb_decide() {
    return base->decide()->get_lit();
}
