#include <utility>

#include "matrix_propagator.h"

size_t hash<raw_term>::operator()(const raw_term& x) const {
    static const hash<term> hash;
    size_t ret = x.FuncID;
    for (const auto* arg: x.Args)
        ret = 31 * ret + hash(*arg);
    return ret;
}

size_t hash<term>::operator()(const term& x) const {
    return 233 * x.solver_id() + x.id();
}

size_t std::hash<term_instance>::operator()(const term_instance& x) const {
    static const hash<term> hash;
    return hash(*x.t) * 133 + x.cpy_idx();
}

void justification::resolve_justification(propagator_base& propagator, vector<literal>& just) const {

    add_range(just, litJust);

    for (auto [from, to] : eqJust) {
        if (from == to)
            continue;

        assert(from->find_root(propagator) == to->find_root(propagator));

        stack<tuple<term_instance*, term_instance*, justification*>> todo;
        vector<justification*> eqJustifications;

        for (auto& c : from->actual_connections) {
            auto* local_to = c.GetOther(from);
            if (to == local_to) {
                c.just.resolve_justification(propagator, just);
                goto next;
            }
            todo.emplace(from, local_to, &c.just);
        }

        while (!todo.empty()) {
            auto [local_from, current, ej] = todo.top();
            todo.pop();
            if (local_from == nullptr) {
                eqJustifications.pop_back();
                continue;
            }

            todo.emplace(nullptr, nullptr, nullptr);
            eqJustifications.push_back(ej);
            assert(!current->actual_connections.empty());

            for (auto& c : current->actual_connections) {
                auto* local_to = c.GetOther(current);
                if (local_to == local_from)
                    continue; // don't go back
                if (local_to == to) {
                    eqJustifications.push_back(&c.just);
                    for (auto* j : eqJustifications) {
                        j->resolve_justification(propagator, just);
                    }
                    goto next;
                }
                todo.emplace(current, local_to, &c.just);
            }
        }

        throw solving_exception("Could not resolve eq-justification");

        next:;
    }
}

string justification::to_string() const {
    stringstream sb;
    for (unsigned i = 0; i < litJust.size(); i++) {
        if (i != 0)
            sb << ", ";
        sb << litJust[i]->to_string();
    }
    if (!litJust.empty() && !eqJust.empty()) {
        sb << ", ";
    }
    for (unsigned i = 0; i < eqJust.size(); i++) {
        if (i != 0)
            sb << ", ";
        sb << eqJust[i].first->to_string() + " == " + eqJust[i].second->to_string();
    }
    return sb.str();
}

#ifndef NDEBUG
string position::to_string() const {
    return lhs->to_string() + "[" + std::to_string(argIdx) + "]  <> " + rhs->to_string() + "[" + std::to_string(argIdx);
}

string less_than::to_string() const {
    return LHS->to_string() + " < " + RHS->to_string();
}
#endif

equality::equality(term_instance* lhs, term_instance* rhs, justification just) : just(std::move(just)) {
    if (lhs->compare_to(rhs) <= 0) {
        LHS = lhs;
        RHS = rhs;
    }
    else {
        LHS = rhs;
        RHS = lhs;
    }
}

disequality::disequality(term_instance* lhs, term_instance* rhs, justification just) : just(just) {
    if (lhs->compare_to(rhs) <= 0) {
        LHS = lhs;
        RHS = rhs;
    }
    else {
        LHS = rhs;
        RHS = lhs;
    }
}

#ifndef NDEBUG
string equality::to_string() const {
    return LHS->to_string() + " == " + RHS->to_string();
}
string disequality::to_string() const {
    return LHS->to_string() + " != " + RHS->to_string();
}
#endif

size_t hash<equality>::operator()(const equality& x) const {
    auto h = (size_t)x.LHS;
    h ^= (size_t)x.RHS + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

size_t hash<less_than>::operator()(const less_than& x) const {
    auto h = (size_t)x.LHS;
    h ^= (size_t)x.RHS + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

unsigned term_instance::cpy_idx() const {
    return origin == nullptr ? 0 : origin->copyIdx;
}

term_instance* term_instance::find_root(propagator_base& propagator) {
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

z3::expr term_instance::to_z3_us() {
    if (z3_expr.has_value())
        return *z3_expr;

#if !defined(NDEBUG)
    z3_expr = fresh_user_constant(t->solver.get_z3_us_sort().ctx(), to_string(), t->solver.get_z3_us_sort());
#else
    z3_expr = fresh_user_constant(t->solver.get_z3_us_sort().ctx(), "term", t->solver.get_z3_us_sort());
#endif
    t->solver.get_complex_solver().set_z3_expr(*z3_expr, this);
    return *z3_expr;
}

z3::expr term_instance::to_z3_adt(matrix_propagator& propagator, z3::context& context, unordered_map<term_instance*, optional<z3::expr>>& map, vector<term_instance*>& terms) {
    optional<z3::expr> e;
    if (tryGetValue(map, this, e))
        return *e;

    z3::expr_vector args(context);
    for (const term* arg: t->Args) {
        args.push_back(arg->get_instance(cpy_idx(), propagator)->to_z3_adt(propagator, context, map, terms));
    }
    if (t->FuncID < 0)
        e = fresh_constant(context, "var", t->solver.get_z3_adt_sort());
    else
        e = t->solver.get_z3_adt_sort().constructors()[t->FuncID](args);
    map.insert(make_pair(this, e));
    terms.push_back(this);
    assert(map.size() == terms.size());
    return *e;
}

const term* term_instance::fully_expand(matrix_propagator& propagator) {
    if (t->is_ground())
        return this->t;
    if (t->is_const()) {
        assert(!t->Args.empty());
        vector<const term*> args;
        for (unsigned i = 0; i < t->Args.size(); i++) {
            args.push_back(get_arg(i, propagator)->fully_expand(propagator));
        }
        return t->solver.make_term(t->FuncID, std::move(args), nullptr);
    }
    term_instance* inst = find_root(propagator);
    if (inst->t->is_const())
        return inst->fully_expand(propagator);
    return inst->t->solver.get_unique_skolem();
}

unsigned term::solver_id() const { return solver.id(); }

term::term(int funcId, vector<const term*> args, simple_adt_solver& solver, unsigned hashId, const indexed_clause* clause) :
        raw_term(funcId, std::move(args)), ast_id(hashId), origin_clause(clause), solver(solver)
#ifndef NDEBUG
        , name(to_string())
#endif
        {
    assert((clause == nullptr) == (funcId >= 0 && all_of(Args.cbegin(), Args.cend(), [](const term* o) { return o->is_ground(); })));
}

term::~term() {
    reset();
}

void term::reset() {
    for (term_instance* inst : instances)
        delete inst;
    instances.clear();
}

term_instance* term::get_instance(unsigned cpy, matrix_propagator& propagator) const {
    if (is_ground())
        cpy = 0;
    for (unsigned i = instances.size(); i <= cpy; i++) {
        instances.push_back(term_instance::new_instance(this, propagator.get_ground(origin_clause, i)));
    }
    return instances[cpy];
}

bool term::seems_possibly_unifiable(const term* rhs, subterm_hint& hint) const {
    // TODO: Just create the equality axiom and check if it is false (cached anyway as well)
    if (FuncID < 0 || rhs->FuncID < 0) {
        hint.add(this, rhs);
        return true;
    }
    if (ast_id == rhs->ast_id && is_ground()) {
        assert(rhs->is_ground());
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
        if (!Args[i]->seems_possibly_unifiable(rhs->Args[i], hint))
            return false;
    }
    return true;
}

string term::to_string() const {
    return solver.pretty_print(this, 0, nullptr);
}

string term::pretty_print(unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const {
    return solver.pretty_print(this, cpyIdx, prettyNames);
}

