#include "propagator_base.h"

size_t std::hash<literal_term*>::operator()(const literal_term* const x) const {
    return (size_t)x;
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

z3::expr literal_term::get_z3(z3_propagator& propagator) {
    return propagator.get_expr(get_var_id());
}

z3::expr false_term::get_z3(z3_propagator& propagator) {
    return propagator.get_ctx().bool_val(false);
}

z3::expr true_term::get_z3(z3_propagator& propagator) {
    return propagator.get_ctx().bool_val(true);
}

const literal not_term::get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) {
    assert(!t->is_true() && !t->is_false());

    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else
        return manager.mk_lit(var_id);
    const formula_term* arg = t->get_lits(propagator, aux);
    aux.emplace_back(std::vector<int>({-var_id, -arg->get_var_id()}));
    aux.emplace_back(std::vector<int>({var_id, arg->get_var_id()}));
    return manager.mk_lit(var_id);
}

z3::expr not_term::get_z3(z3_propagator& propagator) {
    return !t->get_z3(propagator);
}

const literal and_term::get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else {
        literal lit = manager.mk_lit(var_id);
        // assert(connections.empty());
        add_range(lit->connections, connections);
        connections.clear();
        return lit;
    }
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
    literal lit = manager.mk_lit(var_id);
    add_range(lit->connections, connections);
    connections.clear();
    return lit;
}

z3::expr and_term::get_z3(z3_propagator& propagator) {
    z3::expr_vector args(propagator.get_ctx());
    for (formula_term* arg: this->args) {
        args.push_back(arg->get_z3(propagator));
    }
    return z3::mk_and(args);
}

const literal or_term::get_lits(propagator_base& propagator, std::vector<std::vector<int>>& aux) {
    if (var_id == 0)
        var_id = propagator.new_var(OPT("<" + to_string() + ">"));
    else {
        literal lit = manager.mk_lit(var_id);
        assert(connections.empty());
        add_range(lit->connections, connections);
        connections.clear();
        return lit;
    }
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
    literal lit = manager.mk_lit(var_id);
    add_range(lit->connections, connections);
    connections.clear();
    return lit;
}

z3::expr or_term::get_z3(z3_propagator& propagator) {
    z3::expr_vector args(propagator.get_ctx());
    for (formula_term* arg: this->args) {
        args.push_back(arg->get_z3(propagator));
    }
    return z3::mk_or(args);
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

literal formula_manager::mk_lit(unsigned v, bool neg) {
    assert(v != 0);
    /*const auto interpr = propagator->final_interpretation[v - 1];
    if (interpr != undef) {
        return (neg ? unsat : sat) == interpr ? (literal)mk_true() : (literal)mk_false();
    }*/
    literal ret;
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

literal formula_manager::mk_lit(int v) {
    assert(v != 0);
    return mk_lit(abs(v), v < 0);
}

literal formula_manager::mk_not(literal c) {
    if (c->is_false())
        return mk_true();
    if (c->is_true())
        return mk_false();
    return mk_lit(-c->get_var_id());
}

formula_term* formula_manager::mk_not(formula_term* c) {
    if (c->is_literal())
        return mk_not((literal)c);
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
    and_cache.insert(std::make_pair(c, ret));
    return ret;
}

formula_manager::formula_manager(propagator_base* propagator) : propagator(propagator) {
#ifndef NDEBUG
    names.insert(std::make_pair(0, "true"));
#endif
    trueTerm = new true_term(*this);
    trueTerm->fix(true);
    falseTerm = new false_term(*this);
    falseTerm->fix(false);
}

formula_manager::~formula_manager() {
    for (auto* f: id_to_formula) {
        delete f;
    }
}

void formula_manager::register_formula(formula_term* term) {
    id_to_formula.push_back(term);
}
