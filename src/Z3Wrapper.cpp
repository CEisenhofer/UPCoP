#include "propagator_base.h"

#ifndef NDEBUG
void z3_propagator::output_literals(const std::vector<literal>& lit) const {
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

void z3_propagator::propagate_conflict(const std::vector<literal>& just) {
    if (base->is_conflict())
        return;
    // assert(just.size() > 1); // No general problem with that, but this looks suspicious...
    base->set_conflict();
#ifndef NDEBUG
    Log("conflict (hard) [" << incCnt++ << "]: ");
    output_literals(just);
    LogN("");
#endif

    z3::expr_vector aux(*ctx);
    aux.resize(just.size());
    for (unsigned i = 0; i < just.size(); i++) {
        z3::expr e = just[i]->get_z3(*this);
        aux.set(i, e);
    }

    conflict(aux);
}

bool z3_propagator::propagate(const std::vector<literal>& just, literal prop) {
    if (base->is_conflict())
        return false;
    if (prop->is_true())
        return true;
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

    z3::expr_vector aux(*ctx);
    aux.resize(just.size());
    for (unsigned i = 0; i < just.size(); i++) {
        z3::expr e = just[i]->get_z3(*this);
        aux.set(i, e);
    }
    z3::user_propagator_base::propagate(aux, prop->get_z3(*this));
    return true;
}

z3_propagator::z3_propagator(z3::context* ctx, z3::solver* s, propagator_base* base, unsigned timeLeft) : z3::user_propagator_base(s),
        ctx(ctx), s(s), base(base), m(base), assumptions(*ctx), empty_sort_vector(*ctx), idxToZ3(*ctx) {

    register_fixed();
    register_final();
    register_created();

    idxToZ3.push_back(ctx->bool_val(false));
    z3ToIdx.insert(make_pair(ctx->bool_val(false), 0));
    s->set("timeout", timeLeft);
#ifndef NDEBUG
    reset_names();
#endif
}

z3_propagator::~z3_propagator() {
    delete s;
}

static unsigned fixedCnt = 0;

void z3_propagator::fixed(const z3::expr& e, const z3::expr& z3Value) {
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
