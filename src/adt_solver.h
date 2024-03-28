#pragma once
#include "term.h"

struct propagator_base;

class complex_adt_solver {

    vector<string> SortNames;

    unordered_map<string, simple_adt_solver*> nameToSolver;
    unordered_map<literal, equality> exprToEq;
    unordered_map<literal, less_than> exprToLess;
    unordered_map<equality, formula> eqToExpr;
    unordered_map<less_than, formula> lessToExpr;

    unordered_map<z3::expr, term_instance*> exprToTerm;

    matrix_propagator* prop = nullptr;

    vector<simple_adt_solver*> solvers;

public:

    inline unsigned get_sort_cnt() const {
        return SortNames.size();
    }

    complex_adt_solver() = default;

    complex_adt_solver(complex_adt_solver&) = delete;
    complex_adt_solver& operator=(complex_adt_solver&) = delete;

    ~complex_adt_solver();

    inline void set(matrix_propagator* propagator) {
        prop = propagator;
    }

    void clear();

    inline matrix_propagator& propagator() const {
        return *prop;
    }

    simple_adt_solver* new_solver(const string& name);

    string get_solver_name(unsigned solverId) {
        return SortNames[solverId];
    }

    simple_adt_solver* get_solver(const string& name);

    bool asserted(literal e, bool isTrue);

    bool asserted_eq(justification just, term_instance* lhs, term_instance* rhs, bool isTrue) const;
    bool asserted_less(literal e, term_instance* lhs, term_instance* rhs) const;

    bool try_assert_eq(equality info, bool isTrue);

    bool contains_cycle(term_instance* t, term_instance* c) const;
    bool preprocess_equality(term_instance* lhs, term_instance* rhs, vector<equality>& subproblems);
    bool preprocess_less(stack<less_than> stack, vector<less_than>& subproblems, bool& eq);

    bool preprocess_less(term_instance* lhs, term_instance* rhs, vector<less_than>& subproblems, bool& eq) {
        stack<less_than> stack;
        stack.emplace(lhs, rhs);
        return preprocess_less(std::move(stack), subproblems, eq);
    }

    literal make_equality_atom(term_instance* lhs, term_instance* rhs);

    formula make_equality_expr(term_instance* lhs, term_instance* rhs);
    formula make_disequality_expr(term_instance* lhs, term_instance* Rhs);

    literal make_less_atom(term_instance* lhs, term_instance* rhs);

    formula make_less_expr(vector<less_than> subproblems, bool eq);
    formula make_less_expr(term_instance* lhs, term_instance* rhs);

    formula make_greater_eq_expr(term_instance* lhs, term_instance* rhs);

    formula make_less_eq_expr(term_instance* lhs, term_instance* rhs) {
        return make_greater_eq_expr(rhs, lhs);
    }
    formula make_greater_expr(term_instance* lhs, term_instance* rhs) {
        return make_less_expr(rhs, lhs);
    }


    void peek_term(const string& solver, const string& name, int argCnt);

    static bool are_equal(term_instance* lhs, term_instance* rhs);

    void make_z3_us(z3::context& ctx);
    void make_z3_adt(z3::context& ctx);

    void set_z3_expr(const z3::expr& e, term_instance* term) {
        exprToTerm.insert(make_pair(e, term));
    }

    term_instance* get_term(const z3::expr& e) const {
        return exprToTerm.at(e);
    }
};

class simple_adt_solver {

    friend class complex_adt_solver;

    complex_adt_solver& complexSolver;

    optional<z3::sort> z3ADTSort;
    optional<z3::sort> z3USSort;
    const unsigned solverId;
    vector<std::vector<unsigned>> domains;
    vector<string> funcNames;
    vector<string> varNames;

    unordered_map<string, int> nameToId;
    unordered_map<RawTermWrapper, term*> hashCon;

    const term* unique_skolem = nullptr;

    unsigned markIdx = 0;

    void conflict(const justification& just);
    void propagate(const justification& just, formula prop);

    void ensure_founded();


public:

    const term* get_unique_skolem() {
        if (unique_skolem == nullptr) {
            int id = 0;
            if (!tryGetValue(nameToId, string("uSk"), id)) {
                unique_skolem = make_term("uSk", {}, nullptr);
            }
            else {
                unsigned i = 0;
                for (; i <= funcNames.size(); i++) {
                    string name = string("uSk") + std::to_string(i);
                    if (!tryGetValue(nameToId, name, id)) {
                        unique_skolem = make_term(name, {}, nullptr);
                        break;
                    }
                }
                assert(unique_skolem != nullptr);
            }
        }
        return unique_skolem;
    }

    simple_adt_solver(complex_adt_solver& complexSolver, unsigned id) : complexSolver(complexSolver), solverId(id) { }

    ~simple_adt_solver();

    inline matrix_propagator& propagator() const {
        return complexSolver.propagator();
    }

    inline complex_adt_solver& get_complex_solver() const {
        return complexSolver;
    }

#ifndef NDEBUG
    bool is_marking = false;
#endif

    inline void start_mark() {
        assert(!is_marking);
        [[likely]]
        if (markIdx < UINT_MAX) {
            markIdx++;
            return;
        }

        for (auto& [_, t] : hashCon) {
            for (auto& inst : t->instances) {
                inst->marked = 0;
            }
        }
        markIdx = 1;
    }

    inline void end_mark() {
#ifndef NDEBUG
        assert(!is_marking);
        is_marking = false;
#endif
    }

    inline bool mark(term_instance* t) const {
        if (t->marked == markIdx)
            return true;
        t->marked = markIdx;
        return false;
    }

    inline unsigned id() const {
        return solverId;
    }

    inline z3::sort get_z3_us_sort() const {
        assert(z3USSort.has_value());
        return *z3USSort;
    }

    inline z3::sort get_z3_adt_sort() const {
        return *z3ADTSort;
    }

    string pretty_print(const term* t, unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const;

    int peek_term(const string& name, unsigned argCnt);
    int peek_term(const string& name, vector<unsigned> domain);

    inline term* make_term(const string& name, const vector<const term*>& args, const indexed_clause* clause) {
        return make_term(peek_term(name, args.size()), args, clause);
    }

    term* make_term(int id, const vector<const term*>& args, const indexed_clause* clause);
    term* make_term_internal(int id, const vector<const term*>& args, const indexed_clause* clause);
    term* make_var(const string& name, const indexed_clause* clause);
    term* make_var(int idx, const indexed_clause* clause);

    inline int get_id(const string& name) const {
        return nameToId.at(name);
    }

private:

    bool update_diseq(term_instance* b, term_instance* newRoot);

public:

    bool unify_split(term_instance* lhs, term_instance* rhs, justification just);
    bool non_unify_split(term_instance* lhs, term_instance* rhs, const justification& just);
    tri_state test_non_unify_split(term_instance* lhs, term_instance* rhs, justification just);
    bool unify(literal just, term_instance* lhs, term_instance* rhs);
    bool are_equal(term_instance* lhs, term_instance* rhs);
    bool non_unify(term_instance* lhs, term_instance* rhs, const justification& just);
    bool less(literal just, term_instance* lhs, term_instance* rhs);
    tri_state test_less(literal just, term_instance* lhs, term_instance* rhs);


private:

    bool unify(term_instance* lhs, term_instance* rhs, justification& just);
    z3::check_result non_unify(Lazy* lazy);

    bool check_containment_cycle(term_instance* inst, justification& just);
    bool check_containment_cycle(term_instance* inst, term_instance* search, justification& justifications);

    bool is_reachable(term_instance* from, term_instance* to);
    bool check_smaller_cycle(term_instance* start, term_instance* startRoot, term_instance* current, justification& just);
    bool check_diseq_replacement(term_instance* newRoot);
    bool check_less_replacement(term_instance* newRoot);

    bool add_root(term_instance* b, term_instance* newRoot, const equality& eq);
    bool merge_root(term_instance* r1, term_instance* r2, const equality& eq);

public:

    string to_string() const;
};
