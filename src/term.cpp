#include <utility>

#include "matrix_propagator.h"

size_t hash<raw_term>::operator()(const raw_term& x) const {
    static const hash<term> hash;
    size_t ret = x.FuncID;
    for (auto* arg: x.Args)
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

void justification::resolve_justification(simple_adt_solver* adtSolver, vector<literal>& just,
                                          unordered_map<term_instance*, unsigned>& termInstance, vector<unsigned>& parent) const {

    static auto get_id = [](unordered_map<term_instance*, unsigned>& termInstance, vector<unsigned>& parent, term_instance* t) {
        unsigned id = 0;
        if (tryGetValue(termInstance, t, id))
            return id;
        id = termInstance.size();
        termInstance.insert(make_pair(t, id));
        parent.push_back(id);
        return id;
    };

    static auto find = [](vector<unsigned>& parent, unsigned id) {
        unsigned r = id;
        while (r != parent[r]) {
            r = parent[r] = parent[parent[r]];
        }
        return parent[id] = r;
    };

    static auto merge = [](vector<unsigned>& parent, unsigned id1, unsigned id2) {
        parent[find(parent, id1)] = find(parent, id2);
    };

    add_range(just, litJust);
    for (auto [lhs, rhs] : eqJust) {
        unsigned lhsId = get_id(termInstance, parent, lhs);
        unsigned rhsId = get_id(termInstance, parent, rhs);
        unsigned r1 = find(parent, lhsId);
        unsigned r2 = find(parent, rhsId);
        // Avoid finding the same justification over and over again
        if (r1 == r2)
            continue;
        merge(parent, lhsId, rhsId);
        justification j;
        simple_adt_solver::find_just(lhs, rhs, j);
        j.resolve_justification(adtSolver, just, termInstance, parent);
    }
}

void justification::resolve_justification(simple_adt_solver* adtSolver, vector<literal>& just) const {
    unordered_map<term_instance*, unsigned> termInstance;
    vector<unsigned> parent;
    resolve_justification(adtSolver, just, termInstance, parent);
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

#ifndef NDEBUG
string equality::to_string() const {
    return LHS->to_string() + " == " + RHS->to_string();
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

z3::expr term_instance::to_z3(matrix_propagator& propagator, z3::context& context, unordered_map<term_instance*, optional<z3::expr>>& map) {
    optional<z3::expr> e;
    if (tryGetValue(map, this, e))
        return *e;
    z3::expr_vector args(context);
    for (term* arg: t->Args) {
        args.push_back(arg->get_instance(cpy_idx(), propagator)->to_z3(propagator, context, map));
    }
    if (t->FuncID < 0)
        e = FreshConstant(context, "var", t->Solver.get_z3_sort());
    else
        e = t->Solver.get_z3_sort().constructors()[t->FuncID](args);
    map.insert(make_pair(this, e));
    return *e;
}

unsigned term::solver_id() const { return Solver.id(); }

term::term(int funcId, vector<term*> args, simple_adt_solver& solver, unsigned hashId, const indexed_clause* clause) :
        raw_term(funcId, std::move(args)), ast_id(hashId), origin_clause(clause), Solver(solver) {
    assert((clause == nullptr) == (funcId >= 0 && all_of(Args.cbegin(), Args.cend(), [](term* o) { return o->is_ground(); })));
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

bool term::SeemsPossiblyUnifiable(term* rhs, subterm_hint& hint) {
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
        if (!Args[i]->SeemsPossiblyUnifiable(rhs->Args[i], hint))
            return false;
    }
    return true;
}

string term::to_string() const {
    return Solver.pretty_print(this, 0, nullptr);
}

string term::pretty_print(unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const {
    return Solver.pretty_print(this, cpyIdx, prettyNames);
}
