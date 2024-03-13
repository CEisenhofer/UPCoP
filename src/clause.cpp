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

indexed_clause::indexed_clause(unsigned index, vector<indexed_literal*> literals, vector<term*> variables) :
        literals(std::move(literals)), variables(std::move(variables)), Index(index), Ground(
        all_of(this->literals.cbegin(), this->literals.cend(),
               [](const indexed_literal* o1) {
                    return all_of(o1->arg_bases.cbegin(), o1->arg_bases.cend(), [](const auto& o2) { return o2->is_ground(); });
               }
        )) { }

string indexed_clause::to_string(int resolvedLiteralIdx) const {
    if (literals.empty())
        return "false";
    if (literals.size() == 1)
        return literals[0]->to_string();
    stringstream sb;
    sb << '(' << literals[resolvedLiteralIdx]->to_string();
    for (int i = 0; i < literals.size(); i++) {
        if (i == resolvedLiteralIdx)
            continue;
        sb << " || " << literals[i]->to_string();
    }
    sb << ')';
    return sb.str();
}
