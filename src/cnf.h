#pragma once
#include "clause.h"

template<typename T>
struct cnf {

    vector<T> clauses;

    static cnf<clause> get_true() {
        return {};
    }

    static cnf<clause> get_false() {
        return { vector<clause>{{}} };
    }

    static cnf<clause> True;
    static cnf<clause> False;


    inline unsigned size() const {
        return clauses.size();
    }

    inline T& operator[](unsigned i) {
        return clauses[i];
    }

    inline const T& operator[](unsigned i) const {
        return clauses[i];
    }

    cnf() = default;

    cnf(vector<T> clauses) :
        clauses(std::move(clauses)) { }

    cnf(const vector<cnf<T>>& cnfs) {
        unsigned sum = 0;
        for (auto& cnf : cnfs) {
            sum += cnf.clauses.size();
        }
        clauses.reserve(sum);
        for (auto& cnf : cnfs) {
            add_range(clauses, cnf.clauses);
        }
    }

    string to_string() const {
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

