#pragma once
#include "term.h"

struct propagator_base;

class complex_adt_solver {

    vector<string> SortNames;

    unordered_map<string, simple_adt_solver*> nameToSolver;
    unordered_map<literal, equality> exprToEq;
    unordered_map<literal, less_than> exprToLess;
    unordered_map<equality, formula> eqToExpr;
    unordered_map<less_than, literal> lessToExpr;

    matrix_propagator* prop = nullptr;

public:

    vector<simple_adt_solver*> solvers;


    inline unsigned get_sort_cnt() const {
        return SortNames.size();
    }

    complex_adt_solver() = default;

    complex_adt_solver(complex_adt_solver&) = delete;
    complex_adt_solver& operator=(complex_adt_solver&) = delete;

    ~complex_adt_solver();

    void reset(matrix_propagator* propagator);

    inline matrix_propagator& propagator() const {
        return *prop;
    }

    simple_adt_solver* new_solver(const string& name);

    string get_solver_name(unsigned solverId) {
        return SortNames[solverId];
    }

    simple_adt_solver* get_solver(const string& name);

    bool asserted(literal e, bool isTrue);

    bool asserted(literal e, term_instance* lhs, term_instance* rhs, bool isTrue) const;

    bool preprocess_equality(term_instance* lhs, term_instance* rhs, vector<equality>& subproblems);

    formula make_equality_expr(term_instance* lhs, term_instance* rhs);
    formula make_disequality_expr(term_instance* lhs, term_instance* Rhs);

    literal make_less_expr(term_instance* lhs, term_instance* rhs);
    literal make_greater_eq_expr(term_instance* lhs, term_instance* rhs);

    literal make_less_eq_expr(term_instance* lhs, term_instance* rhs) {
        return make_greater_eq_expr(rhs, lhs);
    }
    literal make_greater_expr(term_instance* lhs, term_instance* rhs) {
        return make_less_expr(rhs, lhs);
    }

    void peek_term(const string& solver, const string& name, int argCnt);

    static bool are_equal(term_instance* lhs, term_instance* rhs);
};

class simple_adt_solver {

    friend class complex_adt_solver;

    complex_adt_solver& complexSolver;

    optional<z3::sort> z3Sort;
    const unsigned solverId;
    vector<std::vector<unsigned>> domains;
    vector<string> funcNames;
    vector<string> varNames;

    unordered_map<string, int> nameToId;
    unordered_map<RawTermWrapper, term*> hashCon;

    void conflict(const justification& just);
    void propagate(const justification& just, formula prop);
    bool soft_propagate(const justification& just, literal prop);

public:

    simple_adt_solver(complex_adt_solver& complexSolver, unsigned id) : complexSolver(complexSolver), solverId(id) { }

    ~simple_adt_solver();

    inline matrix_propagator& propagator() const {
        return complexSolver.propagator();
    }

    inline unsigned id() const {
        return solverId;
    }

    string pretty_print(const term* t, unsigned cpyIdx, unordered_map<term_instance*, string>* prettyNames) const;

    int peek_term(const string& name, unsigned argCnt);
    int peek_term(const string& name, vector<unsigned> domain);

    inline term* make_term(const string& name, const vector<term*>& args, const indexed_clause* clause) {
        return make_term(peek_term(name, args.size()), args, clause);
    }

    term* make_term(int id, const vector<term*>& args, const indexed_clause* clause);
    term* make_term_internal(int id, const vector<term*>& args, const indexed_clause* clause);
    term* make_var(const string& name, const indexed_clause* clause);
    term* make_var(int idx, const indexed_clause* clause);

    inline int get_id(const string& name) const {
        return nameToId.at(name);
    }

private:

    bool update_diseq(term_instance* b, term_instance* newRoot);
    bool update_ineq(term_instance* newRoot);

public:
    bool unify_split(literal just, term_instance* lhs, term_instance* rhs);
    bool unify_split(term_instance* lhs, term_instance* rhs, justification& just);
    bool non_unify_split(literal just, term_instance* lhs, term_instance* rhs);
    bool unify(literal just, term_instance* lhs, term_instance* rhs);
    bool are_equal(term_instance* lhs, term_instance* rhs);
    bool non_unify(literal just, term_instance* lhs, term_instance* rhs);
    bool less(literal just, term_instance* lhs, term_instance* rhs, bool eq);


private:

    bool unify(term_instance* lhs, term_instance* rhs, justification& justifications);
    z3::check_result non_unify(Lazy* lazy);


    bool check_cycle(term_instance* inst, justification& justifications);
    bool check_cycle(term_instance* inst, term_instance* search, justification& justifications);
    bool check(term_instance* start, term_instance* current, bool eq, justification& just, vector<term_instance*>& path, bool smaller);


    bool add_root(term_instance* b, term_instance* newRoot, bool incIneq = true);
    bool merge_root(term_instance* r1, term_instance* r2, const equality& eq, bool incIneq = true);

public:
    static void find_just(term_instance* n1, term_instance* n2, justification& minimalJust);

    string to_string() const;
};
