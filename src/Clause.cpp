#include "Clause.h"

Clause::Clause(const z3::expr_vector& exprs, unordered_map<string, unsigned>& nameCache) {
    literals.reserve(exprs.size());
    for (const auto& e : exprs) {
        literals.emplace_back(e, nameCache);
    }
}

Clause::Clause(const Clause& c1, const Clause& c2) {
    literals.reserve(c1.size() + c2.size());
    add_range(literals, c1.literals);
    add_range(literals, c2.literals);

    for (const auto& c : c1.containedVars)
        containedVars.insert(c);
    for (const auto& c : c2.containedVars)
        containedVars.insert(c);
}

IndexedClause::IndexedClause(unsigned index, const pvector<IndexedLiteral>& literals, z3::sort_vector& varSorts) :
        literals(literals), Index(index), VarSorts(varSorts), Ground(
        all_of(literals.cbegin(), literals.cend(),
               [](const IndexedLiteral* o1) {
                    return all_of(o1->ArgBases.cbegin(), o1->ArgBases.cend(), [](const auto& o2) { return o2->Ground; });
               }
        )) {}

string IndexedClause::ToString(int resolvedLiteralIdx) const {
    if (literals.empty())
        return "false";
    if (literals.size() == 1)
        return literals[0]->ToString();
    stringstream sb;
    sb << '(' << literals[resolvedLiteralIdx]->ToString();
    for (int i = 0; i < literals.size(); i++) {
        if (i == resolvedLiteralIdx)
            continue;
        sb << " || " << literals[i]->ToString();
    }
    sb << ')';
    return sb.str();
}
