#include "clause.h"

clause::clause(const z3::expr_vector& exprs, unordered_map<string, unsigned>& nameCache) {
    literals.reserve(exprs.size());
    for (const auto& e : exprs) {
        literals.emplace_back(e, nameCache);
    }
}

clause::clause(const clause& c1, const clause& c2) {
    literals.reserve(c1.size() + c2.size());
    add_range(literals, c1.literals);
    add_range(literals, c2.literals);

    for (const auto& c : c1.containedVars)
        containedVars.insert(c);
    for (const auto& c : c2.containedVars)
        containedVars.insert(c);
}

indexed_clause::indexed_clause(unsigned index, const pvector<indexed_literal>& literals) :
        literals(literals), Index(index), Ground(
        all_of(literals.cbegin(), literals.cend(),
               [](const indexed_literal* o1) {
                    return all_of(o1->arg_bases.cbegin(), o1->arg_bases.cend(), [](const auto& o2) { return o2->Ground; });
               }
        )) {}

string indexed_clause::ToString(int resolvedLiteralIdx) const {
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
