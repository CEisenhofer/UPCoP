#include "CadicalWrapper.h"
#include <chrono>

#ifndef NDEBUG
std::unordered_map<unsigned, std::string> names;
#endif

size_t std::hash<literal_term*>::operator()(const literal_term* const x) const {
    return (size_t) x;
}

bool std::equal_to<literal_term*>::operator()(const literal_term* const x, const literal_term* const y) const {
    return x == y;
}

size_t std::hash<std::vector<formula_term*>>::operator()(const std::vector<formula_term*>& x) const {
    size_t res = 0;
    for (const formula_term* t: x) {
        res = (res * 12979) ^ (size_t) t;
    }
    return res;
}

bool std::equal_to<std::vector<formula_term*>>::operator()(const std::vector<formula_term*>& x,
                                                           const std::vector<formula_term*>& y) const {
    if (x.size() != y.size())
        return false;
    for (unsigned i = 0; i < x.size(); i++) {
        if (x[i] != y[i])
            return false;
    }
    return true;
}

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
        if (!get_value(j, val)) {
            unassigned.push_back(j);
        }
        else if (val != literal_to_polarity(j)) {
            wrong_val.push_back(j);
        }
        Log(literal_to_string(j));
        seen.insert(j);
        if (i + 1 < lit.size())
            Log(", ");
    }
    if (!wrong_val.empty()) {
        for (const auto* j : wrong_val) {
            LogN("Inconsistent interpretation: " << literal_to_string(j) << " is not " << literal_to_polarity(j));
        }
    }
    if (!unassigned.empty()) {
        for (const auto* j : unassigned) {
            LogN("\nUnassigned: " << literal_to_string(j));
        }
    }
    assert(wrong_val.empty() && unassigned.empty());
}
#endif

static unsigned incCnt = 0;

void CaDiCal_propagator::propagate_conflict(const std::vector<literal>& just) {
    if (is_conflict_flag)
        return;
    // assert(just.size() > 1); // No general problem with that, but this looks suspicious...
    is_conflict_flag = true;
#ifndef NDEBUG
    Log("conflict (hard) [" << incCnt++ << "]: ");
    output_literals(just);
    LogN("");
#endif

    std::vector<int> aux;
    aux.reserve(just.size());
    for (literal k: just) {
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

bool CaDiCal_propagator::hard_propagate(const std::vector<literal>& just, formula prop) {
    if (is_conflict_flag)
        return false;
    assert(!prop->is_true());
    if (prop->is_false()) {
        propagate_conflict(just);
        return false;
    }
#ifndef NDEBUG
    Log("Propagating (hard) [" << incCnt++ << "]: ");
    output_literals(just);
    Log(" => ");
    LogN(prop->to_string());
#endif

    std::vector<std::vector<int>> aux;
    const literal_term* c = prop->get_lits(*this, aux);
    aux.emplace_back();
    aux.back().reserve(just.size());
    aux.back().push_back(c->get_lit());
    for (literal k: just) {
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

std::vector<literal> j;

bool CaDiCal_propagator::soft_propagate(const std::vector<literal>& just, literal prop) {
    if (is_conflict_flag)
        return false;
    if (prop->is_true())
        return true;
    if (!soft_justifications[literal_to_idx(prop->get_lit())].empty())
        // Already propagated
        return true;
    if (prop->is_false()) {
        propagate_conflict(just);
        return false;
    }
    bool val = false;
    if (get_value(prop, val)) {
        if (literal_to_polarity(prop) == val)
            // Already assigned
            return true;
        std::vector<literal> just2;
        just2.reserve(just.size() + 1);
        add_range(just2, just);
        just2.push_back(m.mk_not(prop));
        propagate_conflict(just2);
        return false;
    }

        // TODO: Check if it is pending (not sure it is worth it...)
#ifndef NDEBUG
    Log("Propagating (soft) [" << incCnt++ << "]: ");
    output_literals(just);
    Log(" => ");
    LogN(prop->to_string() << " [" << prop->get_lit() << "]");
#endif

    std::vector<int> j;
    j.reserve(just.size() + 1);
    for (literal k: just) {
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

class timeout_terminator : public CaDiCaL::Terminator {
    decltype(std::chrono::high_resolution_clock::now()) stopTime;

public:
    explicit timeout_terminator(unsigned timeLeft) : stopTime(std::chrono::milliseconds(timeLeft) + std::chrono::high_resolution_clock::now()) { }

    bool terminate() override {
        return std::chrono::high_resolution_clock::now() >= stopTime;
    }
};

CaDiCal_propagator::CaDiCal_propagator(unsigned timeLeft) : m(this), solver(new CaDiCaL::Solver()), terminator(new timeout_terminator(timeLeft)) {
    solver->set("ilb", 0);
    solver->set("ilbassumptions", 0);
    solver->set("chrono", 0);
    // solver->set("phase", 0);
    solver->connect_terminator(terminator);
    solver->connect_external_propagator(this);
    reset_names();
}

CaDiCal_propagator::~CaDiCal_propagator() {
    delete solver;
    delete terminator;
}

void CaDiCal_propagator::notify_assignment(const vector<int>& lits) {
    for (int lit : lits) {
        bool value = lit > 0;

        const unsigned id = abs(lit);
        if (!interesting[id - 1])
            // ignore tseitin variables or alike
            continue;

        literal v = m.mk_lit(id);
        LogN("Fixed: " << literal_to_string(v) << " := " << value << " [" << lit << "]");
        assert(hard_propagation_read_idx == 0);
        bool prevValue = false;
        if (get_value(v, prevValue)) {
            assert(prevValue == value);
            return;
        }
        interpretation[id - 1] = value ? sat : unsat;
        undo_stack.emplace_back([this, id]() {
            interpretation[id - 1] = undef;
        });

        fixed(v, value);
        if (is_conflict())
            return;
    }
}

void CaDiCal_propagator::notify_new_decision_level() {
    assert(hard_propagation_read_idx == 0);
    LogN("Pushed " + to_string(undo_stack_limit.size()));
    decision_level++;
    undo_stack_limit.push_back(undo_stack.size());
    soft_propagation_limit.push_back(pending_soft_propagations.size());
    soft_propagation_read_limit.push_back(soft_propagation_read_idx);

    assert(pending_hard_propagations.size() == pending_hard_propagations_idx);
    assert(pending_soft_propagations.size() == soft_propagation_read_idx);
}

void CaDiCal_propagator::notify_backtrack(size_t new_level) {
    assert(decision_level == undo_stack_limit.size());
    if (new_level >= undo_stack_limit.size()) {
        // CaDiCal went crazy - let's ignore
        assert(new_level == 0);
        assert(undo_stack_limit.empty());
        return;
    }
    assert(hard_propagation_read_idx == 0);
    LogN("Pop to " << new_level);
    decision_level = new_level;

    is_conflict_flag = false;

    assert(soft_propagations_explanation_idx == 0);

    const unsigned to = soft_propagation_read_idx; // maybe it conflicted before so just clear up to there
    soft_propagation_read_idx = soft_propagation_read_limit[new_level];
    const unsigned prevPending = soft_propagation_limit[new_level];
    soft_propagation_read_limit.resize(new_level);
    soft_propagation_limit.resize(new_level);

    for (unsigned i = soft_propagation_read_idx; i < to; i++) {
        assert(soft_justifications[literal_to_idx(pending_soft_propagations[i].second)].size() > 1);
        soft_justifications[literal_to_idx(pending_soft_propagations[i].second)].clear();
    }
    pending_soft_propagations.resize(prevPending);
    assert(soft_propagation_read_idx <= pending_soft_propagations.size());

    const unsigned prevAction = undo_stack_limit[new_level];
    undo_stack_limit.resize(new_level);
    while (undo_stack.size() > prevAction) {
        undo_stack.back()();
        undo_stack.pop_back();
    }
}

bool CaDiCal_propagator::cb_check_found_model(const std::vector<int>& model) {
    assert(hard_propagation_read_idx == 0);
    assert(soft_propagation_read_idx == pending_soft_propagations.size());
    assert(!is_conflict());
    final();
    return pending_hard_propagations.size() == pending_hard_propagations_idx &&
            !is_conflict();
}

static int invCnt = 0;

int CaDiCal_propagator::cb_propagate() {
    if (is_conflict())
        return 0;
    invCnt++;
    if (soft_propagation_read_idx >= pending_soft_propagations.size())
        return 0;
    auto& [just, prop] = pending_soft_propagations[soft_propagation_read_idx++];
    int ret = prop;
    const unsigned idx = literal_to_idx(ret);
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
    literal d = decide();
    assert(!has_value(d));
    return d->get_lit();
}

const literal_term* literal_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    return this;
}

const literal_term* not_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    assert(!t->is_true() && !t->is_false());

    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else if (active)
        return manager.mk_lit(var_id);
    else
        propagator.observe_again(var_id);
#ifdef PUSH_POP
    active = true;
    propagator.add_undo([this, &propagator]() { propagator.observe_remove(var_id);  active = false; });
#endif
    const formula_term* arg = t->get_lits(propagator, aux);
    aux.emplace_back(std::vector<int>({-var_id, -arg->get_var_id()}));
    aux.emplace_back(std::vector<int>({var_id, arg->get_var_id()}));
    return manager.mk_lit(var_id);
}

const literal_term* and_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else if (active)
        return manager.mk_lit(var_id);
    else
        propagator.observe_again(var_id);
#ifdef PUSH_POP
    active = true;
    propagator.add_undo([this, &propagator]() { propagator.observe_remove(var_id);  active = false; });
#endif
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    for (int arg: argLits) {
        aux.emplace_back(std::vector<int>({-var_id, arg}));
    }
    if (!positive) {
        std::vector<int> prop;
        prop.reserve(1 + argLits.size());
        prop.push_back((signed) var_id);
        for (int arg: argLits) {
            prop.push_back(-arg);
        }
        aux.emplace_back(std::move(prop));
    }
    return manager.mk_lit(var_id);
}

const literal_term* or_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else if (active)
        return manager.mk_lit(var_id);
    else
        propagator.observe_again(var_id);
#ifdef PUSH_POP
    active = true;
    propagator.add_undo([this, &propagator]() { propagator.observe_remove(var_id);  active = false; });
#endif
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    if (!positive) {
        for (int arg: argLits) {
            aux.emplace_back(std::vector<int>({-arg, (signed) var_id}));
        }
    }
    std::vector<int> prop;
    prop.reserve(1 + argLits.size());
    prop.push_back(-var_id);
    for (int arg: argLits) {
        prop.push_back(arg);
    }
    aux.emplace_back(std::move(prop));
    return manager.mk_lit(var_id);
}

true_term* formula_manager::mk_true() const {
    return trueTerm;
}

false_term* formula_manager::mk_false() const {
    return falseTerm;
}

template<typename T>
inline const T& getX(std::vector<T>& vec, unsigned idx) {
    if (vec.size() <= idx) {
        if (vec.capacity() <= idx)
            vec.reserve(2 * idx + 1);
        vec.resize(idx + 1);
    }
    return vec[idx];
}

literal_term* formula_manager::mk_lit(unsigned v, bool neg) {
    assert(v != 0);
    literal_term* ret;
    if (neg) {
        ret = getX(neg_cadical_to_formula, v);
        if (ret != nullptr)
            return ret;
        return neg_cadical_to_formula[v] = new literal_term(*this, v, true);
    }
    ret = getX(cadical_to_formula, v);
    if (ret != nullptr)
        return ret;
    return cadical_to_formula[v] = new literal_term(*this, v, neg);
}

literal_term* formula_manager::mk_lit(int v) {
    assert(v != 0);
    return mk_lit(abs(v), v < 0);
}

literal_term* formula_manager::mk_not(literal_term* c) {
    if (c->is_false())
        return mk_true();
    if (c->is_true())
        return mk_false();
    return mk_lit(-c->get_var_id());
}

formula_term* formula_manager::mk_not(formula_term* c) {
    if (c->is_literal())
        return mk_not((literal_term*)c);
    auto it = not_cache.find(c);
    if (it != not_cache.end())
        return it->second;
    formula_term* ret = c->negate();
    not_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_term* formula_manager::mk_or(std::vector<formula_term*> c, bool positive) {
    sort(c.begin(), c.end(), [](formula_term* a, formula_term* b) {
        return a->get_ast_id() < b->get_ast_id();
    });
    int j = 0;
    const unsigned sz = c.size();
    formula_term* prev = nullptr;
    for (unsigned i = 0; i < sz; i++) {
        if (c[i]->is_true())
            return mk_true();
        if (c[i]->is_false())
            continue;
        if (c[i] == prev)
            continue;
        if (j != i)
            c[j] = c[i];
        prev = c[i];
        j++;
    }
    if (j == 0)
        return mk_false();
    if (j == 1)
        return c[0];
    c.resize(j);
    or_term* ret = nullptr;
    if (tryGetValue(or_cache, c, ret)) {
        assert(ret->is_positive() == positive);
        return ret;
    }
    ret = new or_term(*this, c, positive);
#ifndef NDEBUG
    for (const auto& n : names) {
        assert(n.second != ret->to_string());
    }
#endif
    or_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_term* formula_manager::mk_and(std::vector<formula_term*> c, bool positive) {
    sort(c.begin(), c.end(), [](formula_term* a, formula_term* b) {
        return a->get_ast_id() < b->get_ast_id();
    });
    int j = 0;
    const unsigned sz = c.size();
    formula_term* prev = nullptr;
    for (unsigned i = 0; i < sz; i++) {
        if (c[i]->is_false())
            return mk_false();
        if (c[i]->is_true())
            continue;
        if (c[i] == prev)
            continue;
        if (j != i)
            c[j] = c[i];
        prev = c[i];
        j++;
    }
    if (j == 0)
        return mk_true();
    if (j == 1)
        return c[0];
    c.resize(j);
    and_term* ret = nullptr;
    if (tryGetValue(and_cache, c, ret)) {
        assert(ret->is_positive() == positive);
        return ret;
    }
    ret = new and_term(*this, c, positive);
#ifndef NDEBUG
    for (const auto& n : names) {
        assert(n.second != ret->to_string());
    }
#endif
    and_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_manager::formula_manager(CaDiCal_propagator* propagator) : propagator(propagator) {
#ifndef NDEBUG
    names.insert(std::make_pair(0, "false"));
#endif
    trueTerm = new true_term(*this);
    falseTerm = new false_term(*this);
}

formula_manager::~formula_manager() {
    for (auto* f: id_to_formula) {
        delete f;
    }
}

void formula_manager::register_formula(formula_term* term) {
    id_to_formula.push_back(term);
}
