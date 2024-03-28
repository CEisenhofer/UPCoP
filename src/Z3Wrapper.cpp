#include "propagator_base.h"

#ifndef NDEBUG
static void onClauseEvent(z3::expr const& proof, std::vector<unsigned> const& deps, z3::expr_vector const& clause) {
    if (proof.decl().name().str() == "tseitin" || proof.decl().name().str() == "del")
        return;
    LogN("Proof: " << proof.to_string() << " clause: " << clause.to_string());
}
#endif

#ifndef NDEBUG
void z3_propagator::output_literals(const justification& just) const {
    std::vector<literal> unassigned;
    std::vector<literal> wrong_val;
    std::unordered_set<literal> seen;
    for (unsigned i = 0; i < just.litJust.size(); i++) {
        literal j = just.litJust[i];
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
        if (i + 1 < just.litJust.size() || !just.eqJust.empty() || just.diseqJust.first != nullptr)
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

    unsigned last = 0;
    for (unsigned i = just.eqJust.size(); i > 0; i--) {
        if (just.eqJust[i - 1].first != just.eqJust[i - 1].second) {
            last = i;
            break;
        }
    }

    for (unsigned i = 0; i < last; i++) {
        const auto& eq = just.eqJust[i];
        if (eq.first == eq.second)
            continue;
        // Our e-solver might conflict before merging...
        // assert(eq.first->find_root(*base) == eq.second->find_root(*base));
        Log(eq.first->to_string() << " == " << eq.second->to_string());

        if (i + 1 < last || just.diseqJust.first != nullptr)
            Log(", ");
    }
    assert((just.diseqJust.first == nullptr) == (just.diseqJust.second == nullptr));
    if (just.diseqJust.first != nullptr) {
        Log(just.diseqJust.first->to_string() << " != " << just.diseqJust.second->to_string());
    }
}
#endif

static unsigned incCnt = 0;

void z3_propagator::propagate_conflict(const justification& just) {
    if (base->is_conflict())
        return;
    // assert(just.size() > 1); // No general problem with that, but this looks suspicious...
    base->set_conflict();
#ifndef NDEBUG
    Log("conflict [" << incCnt++ << "]: ");
    output_literals(just);
    LogN("");
#endif

    z3::expr_vector lits(*ctx);
    lits.resize(just.litJust.size());
    for (unsigned i = 0; i < just.litJust.size(); i++) {
        z3::expr e = get_expr(abs(just.litJust[i]->get_lit()));
        lits.set(i, e);
    }
    z3::expr_vector lhs(*ctx);
    z3::expr_vector rhs(*ctx);
    for (unsigned i = 0; i < just.eqJust.size(); i++) {
        if (just.eqJust[i].first == just.eqJust[i].second)
            continue;
        lhs.push_back(just.eqJust[i].first->to_z3_us());
        rhs.push_back(just.eqJust[i].second->to_z3_us());
    }

    if (just.diseqJust.first == nullptr)
        conflict(lits, lhs, rhs);
    else
        z3::user_propagator_base::propagate(lits, lhs, rhs, just.diseqJust.first->to_z3_us() == just.diseqJust.first->to_z3_us());
}

bool z3_propagator::propagate(const justification& just, literal prop) {
    if (base->is_conflict())
        return false;
    if (prop->is_true())
        return true;
    if (prop->is_false()) {
        propagate_conflict(just);
        return false;
    }
#ifndef NDEBUG
    Log("Propagating [" << incCnt++ << "]: ");
    output_literals(just);
    Log(" => ");
    LogN(prop->to_string());
#endif

    z3::expr_vector lits(*ctx);
    lits.resize(just.litJust.size());
    for (unsigned i = 0; i < just.litJust.size(); i++) {
        z3::expr e = get_expr(abs(just.litJust[i]->get_lit()));
        lits.set(i, e);
    }
    z3::expr_vector lhs(*ctx);
    z3::expr_vector rhs(*ctx);
    for (unsigned i = 0; i < just.eqJust.size(); i++) {
        if (just.eqJust[i].first == just.eqJust[i].second)
            continue;
        lhs.push_back(just.eqJust[i].first->to_z3_us());
        rhs.push_back(just.eqJust[i].second->to_z3_us());
    }

    if (just.diseqJust.first == nullptr)
        z3::user_propagator_base::propagate(lits, lhs, rhs, prop->get_z3(*this));
    else
        z3::user_propagator_base::propagate(lits, lhs, rhs, (just.diseqJust.first->to_z3_us() == just.diseqJust.first->to_z3_us()) || prop->get_z3(*this));

    return true;
}

z3_propagator::z3_propagator(z3::context* ctx, z3::solver* s, propagator_base* base, unsigned timeLeft) : z3::user_propagator_base(s),
        ctx(ctx), s(s), base(base), m(base), assumptions(*ctx), empty_sort_vector(*ctx), idxToZ3(*ctx)
#if !defined(NDEBUG) && false
        , onClauseEh(onClauseEvent), onClause(*s, onClauseEh)
#endif
        {

    s->set("random_seed", 1u);

    register_fixed();
    register_final();
    register_eq();
    register_diseq();
    register_created();

    idxToZ3.push_back(ctx->bool_val(false));
    z3ToIdx.insert(make_pair(ctx->bool_val(false), 0));
    s->set("timeout", timeLeft);
#ifndef NDEBUG
    reset_names();
#endif
}

static unsigned fixedCnt = 0;

void z3_propagator::fixed(const z3::expr& e, const z3::expr& z3Value) {

    if (base->is_conflict())
        return;

    assert(z3Value.is_true() || z3Value.is_false());
    assert(e.is_bool());
    bool value = z3Value.is_true();

    const unsigned id = z3ToIdx.at(e);

    fixedCnt++;
    literal v = m.mk_lit((int)id);
    LogN("Fixed [" << fixedCnt << "]: " << v->to_string() << " := " << value << " [" << e.to_string() << " = " << z3Value.to_string() << "]");
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

void z3_propagator::eq(const z3::expr& lhs, const z3::expr& rhs) {
    if (base->is_conflict() || lhs.is_bool())
        return;
    term_instance* lhsTerm = base->term_solver.get_term(lhs);
    term_instance* rhsTerm = base->term_solver.get_term(rhs);

    LogN("Eq: " << lhsTerm->to_string() << " = " << rhsTerm->to_string());
    equality eq(lhsTerm, rhsTerm);
    eq.just.eqJust.emplace_back(lhsTerm, rhsTerm);
    base->term_solver.try_assert_eq(std::move(eq), true);
}

void z3_propagator::diseq(const z3::expr& lhs, const z3::expr& rhs) {
    if (base->is_conflict() || lhs.is_bool())
        return;
    term_instance* lhsTerm = base->term_solver.get_term(lhs);
    term_instance* rhsTerm = base->term_solver.get_term(rhs);

    LogN("Diseq: " << lhsTerm->to_string() << " != " << rhsTerm->to_string());
    equality eq(lhsTerm, rhsTerm);
    eq.just.diseqJust = make_pair(lhsTerm, rhsTerm);
    base->term_solver.try_assert_eq(std::move(eq), false);
}

void z3_propagator::push() {
    LogN("Pushed " + to_string(undo_stack_limit.size()));
    undo_stack_limit.push_back(base->get_undo().size());
}

void z3_propagator::pop(unsigned lvl) {
    assert(undo_stack_limit.size() >= lvl);
    unsigned new_level = undo_stack_limit.size() - lvl;
    if (new_level >= undo_stack_limit.size()) {
        // CaDiCal went crazy - let's ignore
        assert(new_level == 0);
        assert(undo_stack_limit.empty());
        return;
    }
    LogN("Pop to " << new_level);

    base->clear_conflict();

    const unsigned prevAction = undo_stack_limit[new_level];
    undo_stack_limit.resize(new_level);
    vector<action>& undo_stack = base->get_undo();
    while (undo_stack.size() > prevAction) {
        undo_stack.back()();
        undo_stack.pop_back();
    }
}

void z3_propagator::final() {
    assert(!base->is_conflict());
    base->final();
}
