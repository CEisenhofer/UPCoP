#pragma once
#include "Clause.h"

template<typename T>
struct CNF {

    static CNF<Clause> GetTrue() {
        return {};
    }

    static CNF<Clause> GetFalse() {
        return { vector<Clause>(), vector<Clause>{{}} };
    }

    static CNF<Clause> True;
    static CNF<Clause> False;

    vector<T> nonConjectureClauses;
    vector<T> conjectureClauses;

    inline unsigned size() const {
        return nonConjectureClauses.size() + conjectureClauses.size();
    }

    inline T& operator[](unsigned i) {
        return i < nonConjectureClauses.size() ? nonConjectureClauses[i] :
               conjectureClauses[i - nonConjectureClauses.size()];
    }

    inline const T& operator[](unsigned i) const {
        return i < nonConjectureClauses.size() ? nonConjectureClauses[i] :
               conjectureClauses[i - nonConjectureClauses.size()];
    }

    CNF() : nonConjectureClauses(), conjectureClauses() { }

    CNF(vector<T> nonConjectureClauses, vector<T> conjectureClauses) :
        nonConjectureClauses(std::move(nonConjectureClauses)), conjectureClauses(std::move(conjectureClauses)) { }

    CNF(vector<T> nonConjectureClauses) : nonConjectureClauses(std::move(nonConjectureClauses)), conjectureClauses() { }

    CNF(const vector<CNF<T>>& cnfs) : nonConjectureClauses(), conjectureClauses() {
        unsigned conjSum = 0, nonConjSum = 0;
        for (auto& cnf : cnfs) {
            conjSum += cnf.conjectureClauses.size();
            nonConjSum += cnf.nonConjectureClauses.size();
        }
        nonConjectureClauses.reserve(nonConjSum);
        for (auto& cnf : cnfs) {
            add_range(nonConjectureClauses, cnf.nonConjectureClauses);
            add_range(conjectureClauses, cnf.conjectureClauses);
        }
    }

    inline bool IsConjecture(unsigned idx) const {
        return idx >= nonConjectureClauses.size();
    }

    string ToString() const {
        if (size() == 0)
            return "true";
        std::stringstream sb;
        sb << this->operator[](0).to_string();
        for (unsigned i = 1; i < size(); i++) {
            sb << " && " << this->operator[](i).to_string();
        }
        return sb.str();
    }
};

