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

string Literal::ToString() const {
    return PropagatorBase::PrettyPrintLiteral(this, 0, nullptr);
}
