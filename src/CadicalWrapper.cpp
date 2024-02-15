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

void CaDiCalPropagator::propagate_conflict(std::vector<literal> just) {
    if (is_conflict)
        return;
    is_conflict = true;
#ifndef NDEBUG
    Log("Conflict: ");
    for (unsigned i = 0; i < just.size(); i++) {
        literal j = just[i];
        auto it = interpretation.find(j);
        assert(it != interpretation.end());
        assert(it->second == literal_to_polarity(j));
        Log(literal_to_string(j));
        if (i + 1 < just.size())
            Log(", ");
    }
    LogN("");

    std::vector<int> j;
    j.reserve(just.size());
    for (literal k: just) {
        j.push_back(-k->get_lit());
    }
#else
    for (literal& k : just) {
        k = -k;
    }
    std::vector<int>& j = just;
#endif
    propagations.emplace_back(std::move(j), nullptr);
}

void CaDiCalPropagator::propagate(const std::vector<literal>& just, formula_term* prop) {
    if (is_conflict)
        return;
    assert(!prop->is_true());
    if (prop->is_false())
        return propagate_conflict(just);
#ifndef NDEBUG
    Log("Propagating: ");
    for (unsigned i = 0; i < just.size(); i++) {
        literal j = just[i];
        auto it = interpretation.find(j);
        assert(it != interpretation.end());
        assert(it->second == literal_to_polarity(j));
        Log(literal_to_string(j));
        if (i + 1 < just.size())
            Log(", ");
    }
    Log(" => ");
    LogN(prop->to_string());
#endif

    std::vector<std::pair<std::vector<int>, formula>> aux;
    const literal_term* c = prop->get_lits(*this, aux);
    aux.emplace_back();
    aux.back().first.reserve(just.size());
    aux.back().first.push_back(c->get_lit());
    for (literal k: just) {
        aux.back().first.push_back(-k->get_lit());
    }
    // aux.back().second = prop; -- not required; the get_lits should do that

    for (auto& k: aux) {
        propagations.emplace_back(std::move(k));
    }
}

void CaDiCalPropagator::reinit_solver() {
    // Reset everything done so far
    undoStackSize.resize(0);
    while (!undoStack.empty()) {
        undoStack.back()();
        undoStack.pop_back();
    }
    delete solver; // now safe to do a hard reset of CaDiCaL
    solver = new CaDiCaL::Solver();
    solver->connect_external_propagator(this);
    // reintroduce all terms used so far
    for (auto* formula : m.id_to_formula) {
        if (formula->get_var_id() != 0)
            solver->add_observed_var(formula->get_var_id());
    }
}

void CaDiCalPropagator::notify_assignment(int lit, bool is_fixed) {
    bool value = lit > 0;

    literal v = m.mk_lit(abs(lit));
    LogN("Fixed: " << literal_to_string(v) << " = " << value << " [" << is_fixed << "]");

    assert(propagationReadIdx == 0);
    assert(interpretation.find(v) == interpretation.end());
    interpretation.insert(std::make_pair(v, value));
    undoStack.emplace_back([this, v]() {
        interpretation.erase(v);
    });

    fixed(v, value);
}

void CaDiCalPropagator::notify_new_decision_level() {
    LogN("Push");
    undoStackSize.push_back(undoStack.size());
}

void CaDiCalPropagator::notify_backtrack(size_t new_level) {
    LogN("Pop: " << (undoStackSize.size() - new_level));
    const unsigned prev = undoStackSize[new_level];
    undoStackSize.resize(new_level);
    while (undoStack.size() > prev) {
        undoStack.back()();
        undoStack.pop_back();
    }

    assert(propagations.size() >= propagationIdx);
    while (propagations.size() > propagationIdx) {
        if (propagations.back().second != nullptr)
            propagations.back().second->reset_aux();
        propagations.pop_back();
    }
}

bool CaDiCalPropagator::cb_check_found_model(const std::vector<int>& model) {
    assert(propagationReadIdx == 0);
    final();
    return true;
}

bool CaDiCalPropagator::cb_has_external_clause() {
    return propagationIdx < propagations.size();
}

int CaDiCalPropagator::cb_add_external_clause_lit() {
    assert(cb_has_external_clause());
    auto& toAdd = propagations[propagationIdx];
    if (propagationReadIdx >= toAdd.first.size()) {
        if (toAdd.second != nullptr)
            toAdd.second->fix_aux(); // from now on the aux literal is uniquely defined and used
        propagationIdx++;
        propagationReadIdx = 0;
        return 0;
    }
    return toAdd.first[propagationReadIdx++];
}

const literal_term* literal_term::get_lits(CaDiCalPropagator& propagator, std::vector<std::pair<std::vector<int>, formula>>& aux) {
    return this;
}

const literal_term* not_term::get_lits(CaDiCalPropagator& propagator, std::vector<std::pair<std::vector<int>, formula>>& aux) {
    assert(!t->is_true() && !t->is_false());

    if (var_id != 0)
        return manager.mk_lit(var_id);
    var_id = propagator.new_observed_var("proxy: " + to_string());
    const formula_term* arg = t->get_lits(propagator, aux);
    aux.push_back(std::make_pair(std::vector<int>({-var_id, -arg->get_var_id()}), nullptr));
    aux.push_back(std::make_pair(std::vector<int>({var_id, arg->get_var_id()}), this));
    return manager.mk_lit(var_id);
}

const literal_term* and_term::get_lits(CaDiCalPropagator& propagator, std::vector<std::pair<std::vector<int>, formula>>& aux) {
    if (auxLit.id != 0)
        return manager.mk_lit(auxLit.id);
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    auxLit.id = propagator.new_observed_var("proxy: " + to_string());
    for (int arg: argLits) {
        aux.emplace_back(std::vector<int>({-auxLit.id, arg}), nullptr);
    }
    std::vector<int> prop;
    prop.reserve(1 + argLits.size());
    prop.push_back((signed)auxLit.id);
    for (int arg: argLits) {
        prop.push_back(-arg);
    }
    aux.emplace_back(std::move(prop), this);
    return manager.mk_lit(auxLit.id);
}

const literal_term* or_term::get_lits(CaDiCalPropagator& propagator, std::vector<std::pair<std::vector<int>, formula>>& aux) {
    if (auxLit.id != 0)
        return manager.mk_lit(auxLit.id);
    assert(args.size() > 1);
    std::vector<int> argLits;
    argLits.reserve(args.size());
    for (const auto& arg: args) {
        const auto* v = arg->get_lits(propagator, aux);
        argLits.push_back(v->get_lit());
    }
    auxLit.id = propagator.new_observed_var("proxy: " + to_string());
    for (int arg: argLits) {
        aux.emplace_back(std::vector<int>({-arg, (signed)auxLit.id}), nullptr);
    }
    std::vector<int> prop;
    prop.reserve(1 + argLits.size());
    prop.push_back(-auxLit.id);
    for (int arg: argLits) {
        prop.push_back(arg);
    }
    aux.emplace_back(std::move(prop), this);
    return manager.mk_lit(auxLit.id);
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
    literal_term* ret = nullptr;
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
    names.insert(std::make_pair(0, "false"));
    trueTerm = new true_term(*this);
    falseTerm = new false_term(*this);
}

formula_manager::~formula_manager() {
    for (auto* f: id_to_formula) {
        delete f;
    }
}
