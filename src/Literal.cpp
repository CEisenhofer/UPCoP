#include "PropagatorBase.h"

Literal::Literal(z3::expr e, unordered_map<string, unsigned>& nameCache) : ArgBases(), InitExprs({ e.ctx() }) {
    if (e.is_not()) {
        polarity = false;
        e = e.arg(0);
    }
    else {
        polarity = true;
    }
    name = e.decl().name().str();
    if (!tryGetValue(nameCache, name, nameID)) {
        nameID = nameCache.size();
        nameCache.insert(make_pair(name, nameID));
    }
    unsigned sz = e.num_args();
    for (unsigned i = 0; i < sz; i++) {
        InitExprs->push_back(e.arg(i));
    }
}

z3::expr_vector Literal::GetInstances(const z3::expr_vector& args) {
    z3::expr_vector ret(args.ctx());
    ret.resize(ArgBases.size());
    for (unsigned i = 0; i < ArgBases.size(); i++) {
        assert(ArgBases[i]->Z3Expr.has_value());
        z3::expr e = ArgBases[i]->Z3Expr->substitute(args);
        ret.set(i, e);
    }
    return ret;
}

string Literal::ToString() const {
    return PropagatorBase::PrettyPrintLiteral(this, 0, nullptr);
}
