#include "CadicalWrapper.h"
#include <iostream>

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
    for (unsigned i = 0; i < lit.size(); i++) {
        literal j = lit[i];
        auto it = interpretation.find(j);
        if (it == interpretation.end()){
            unassigned.push_back(j);
        }
        else if (it->second != literal_to_polarity(j)) {
            wrong_val.push_back(j);
        }
        Log(literal_to_string(j));
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
            LogN("Unassigned: " << literal_to_string(j));
        }
    }
    assert(wrong_val.empty() && unassigned.empty());
}
#endif

static int incCnt = 0;

void CaDiCal_propagator::propagate_conflict(const std::vector<literal>& just) {
    if (is_conflict_flag)
        return;
    incCnt++;
    assert(just.size() > 1); // No general problem with that, but this looks suspicious...
    is_conflict_flag = true;
#ifndef NDEBUG
    Log("Conflict (hard) [" << incCnt++ << "]: ");
    output_literals(just);
    LogN("");
#endif

    std::vector<int> aux;
    aux.reserve(just.size());
    for (literal k: just) {
        aux.push_back(-k->get_lit());
    }
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
        pending_hard_propagations.emplace_back(std::move(k));
    }
    prev_propagations.insert(aux.back());
    return true;
}

bool CaDiCal_propagator::soft_propagate(const std::vector<literal>& just, literal prop) {
    if (is_conflict_flag)
        return false;
    if (!soft_justifications[literal_to_idx(prop->get_lit())].empty())
        // Already propagated
        return true;

    // TODO: Check if it is pending (not sure it is worth it...)
#ifndef NDEBUG
    Log("Propagating (soft) [" << incCnt++ << "]: ");
    output_literals(just);
    Log(" => ");
    LogN(prop->to_string());
#endif

    std::vector<int> j;
    j.reserve(just.size() + 1);
    for (literal k: just) {
        j.push_back(-k->get_lit());
    }
    const int propLit = prop->get_lit();
    j.push_back(propLit);
    pending_soft_propagations.emplace_back(std::move(j), propLit);
    return true;
}

void CaDiCal_propagator::init_solver() {
    solver = new CaDiCaL::Solver();
    solver->set("ilb", 0);
    solver->set("ilbassumptions", 0);
    solver->connect_external_propagator(this);
}

void CaDiCal_propagator::notify_assignment(const vector<int>& lits) {
    for (int lit : lits) {
        bool value = lit > 0;

        literal v = m.mk_lit(abs(lit));
        LogN("Fixed: " << literal_to_string(v) << " := " << value << " [" << lit << "]");
        assert(hard_propagation_read_idx == 0);
        assert(interpretation.find(v) == interpretation.end());
        interpretation.insert(std::make_pair(v, value));
        undo_stack.emplace_back([this, v]() {
            interpretation.erase(v);
        });

        fixed(v, value);
        if (is_conflict_flag)
            return;
    }
}

void CaDiCal_propagator::notify_new_decision_level() {
    assert(hard_propagation_read_idx == 0);
    LogN("Pushed " + to_string(undo_stack_limit.size()));
    undo_stack_limit.push_back(undo_stack.size());
    soft_propagation_limit.push_back(soft_propagation_undo.size());

    assert(pending_hard_propagations.size() == pending_hard_propagations_idx);
    assert(pending_soft_propagations.empty());
}

void CaDiCal_propagator::notify_backtrack(size_t new_level) {
    assert(hard_propagation_read_idx == 0);
    LogN("Pop to " << new_level);

    is_conflict_flag = false;

    soft_propagation_read_idx = 0;
    pending_soft_propagations.clear();
    const unsigned prevJust = soft_propagation_limit[new_level];
    soft_propagation_limit.resize(new_level);
    for (unsigned i = prevJust; i < soft_propagation_undo.size(); i++) {
        soft_justifications[soft_propagation_undo[i]].clear();
    }
    soft_propagation_undo.resize(prevJust);

    const unsigned prevAction = undo_stack_limit[new_level];
    undo_stack_limit.resize(new_level);
    while (undo_stack.size() > prevAction) {
        undo_stack.back()();
        undo_stack.pop_back();
    }
}

bool CaDiCal_propagator::cb_check_found_model(const std::vector<int>& model) {
    assert(hard_propagation_read_idx == 0);
    assert(soft_propagation_read_idx == 0);
    assert(!is_conflict());
    final();
    return pending_hard_propagations.size() == pending_hard_propagations_idx &&
            !is_conflict();
}

int CaDiCal_propagator::cb_propagate() {
    if (is_conflict())
        return 0;
    if (pending_soft_propagations.empty())
        return 0;
    auto& [just, prop] = pending_soft_propagations.back();
    int ret = prop;
    soft_justifications[literal_to_idx(ret)] = std::move(just);
    soft_propagation_undo.push_back(literal_to_idx(ret));
    pending_soft_propagations.pop_back();
    return ret;
}

int CaDiCal_propagator::cb_add_reason_clause_lit(int propagated_lit) {
    unsigned idx = literal_to_idx(propagated_lit);
    assert(soft_justifications[idx].size() > 0);
    if (soft_propagation_read_idx < soft_justifications[idx].size())
        return soft_justifications[idx][soft_propagation_read_idx++];
    soft_propagation_read_idx = 0;
    return 0;
}


bool CaDiCal_propagator::cb_has_external_clause(bool& is_forgettable) {
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

const literal_term* literal_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    return this;
}

const literal_term* not_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    assert(!t->is_true() && !t->is_false());
    if (var_id != 0)
        return manager.mk_lit(var_id);
    var_id = propagator.new_observed_var(OPT("<" + to_string() + ">"));
    const formula_term* arg = t->get_lits(propagator, aux);
    aux.emplace_back(std::vector<int>({-var_id, -arg->get_var_id()}));
    aux.emplace_back(std::vector<int>({var_id, arg->get_var_id()}));
    return manager.mk_lit(var_id);
}

const literal_term* and_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id != 0)
        return manager.mk_lit(var_id);
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    var_id = propagator.new_observed_var(OPT("<" + to_string() + ">"));
    for (int arg: argLits) {
        aux.emplace_back(std::vector<int>({-var_id, arg}));
    }
    std::vector<int> prop;
    prop.reserve(1 + argLits.size());
    prop.push_back((signed)var_id);
    for (int arg: argLits) {
        prop.push_back(-arg);
    }
    aux.emplace_back(std::move(prop));
    return manager.mk_lit(var_id);
}

const literal_term* or_term::get_lits(CaDiCal_propagator& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id != 0)
        return manager.mk_lit(var_id);
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    var_id = propagator.new_observed_var(OPT("<" + to_string() + ">"));
    for (int arg: argLits) {
        aux.emplace_back(std::vector<int>({-arg, (signed)var_id}));
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
inline void setX(unsigned idx, std::vector<T>& vec, T v) {
    if (vec.size() <= idx) {
        if (vec.capacity() <= idx)
            vec.reserve(2 * idx + 1);
        vec.resize(idx + 1);
    }
    vec[idx] = v;
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
    auto* ret = new not_term(*this, c);
    not_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_term* formula_manager::mk_or(std::vector<formula_term*> c) {
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
    auto it = or_cache.find(c);
    if (it != or_cache.end())
        return it->second;
    auto* ret = new or_term(*this, c);
    or_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_term* formula_manager::mk_and(std::vector<formula_term*> c) {
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
    auto it = and_cache.find(c);
    if (it != and_cache.end())
        return it->second;
    auto* ret = new and_term(*this, c);
    and_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_manager::formula_manager() {
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
