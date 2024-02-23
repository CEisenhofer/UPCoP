#pragma once
#include "clause.h"

template<typename T>
struct cnf {

    static cnf<clause> GetTrue() {
        return {};
    }

    static cnf<clause> GetFalse() {
        return {vector<clause>(), vector<clause>{{}} };
    }

    static cnf<clause> True;
    static cnf<clause> False;

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

    cnf() : nonConjectureClauses(), conjectureClauses() { }

    cnf(vector<T> nonConjectureClauses, vector<T> conjectureClauses) :
        nonConjectureClauses(std::move(nonConjectureClauses)), conjectureClauses(std::move(conjectureClauses)) { }

    cnf(vector<T> nonConjectureClauses) : nonConjectureClauses(std::move(nonConjectureClauses)), conjectureClauses() { }

    cnf(const vector<cnf<T>>& cnfs) : nonConjectureClauses(), conjectureClauses() {
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

    inline bool is_conjecture(unsigned idx) const {
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

