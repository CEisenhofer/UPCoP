#include "propagator_base.h"

fo_literal::fo_literal(z3::expr e, unordered_map<string, unsigned>& nameCache) : arg_bases(), InitExprs({e.ctx() }) {
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

string fo_literal::ToString() const {
    return propagator_base::PrettyPrintLiteral(this, 0, nullptr);
}
