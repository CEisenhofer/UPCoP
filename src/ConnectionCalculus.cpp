#include "ConnectionCalculus.h"
#include "CLIParser.h"
#include "clause.h"
#include "cnf.h"
#include "utils.h"
#include "adt_solver.h"
#include "matrix_propagator.h"
#include <fstream>
#include <z3++.h>

#if !defined(_WIN32) && !defined(_WIN64)

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#endif

const term* variable_abstraction::apply(const vector<const term*>& args) const {
    assert(args.empty());
    return var;
}

const term* term_abstraction::apply(const vector<const term*>& args) const {
    const indexed_clause* cl = nullptr;
    for (auto* arg : args) {
        assert(cl == nullptr || arg->clause() == nullptr || cl == arg->clause());
        if (arg->clause() != nullptr)
            cl = arg->clause();
    }
    auto* t = solver->make_term(termId, args, cl);
    return t;
}

int main(int argc, char* argv[]) {

    ProgParams progParams;
    parse_params(argc, argv, progParams);
    /*if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        Console.BufferHeight = 20000;
    }*/
    tri_state res = solve(argv[argc - 1], progParams, false);
    switch (res) {
        case undef:
            return -1;
        case sat:
            return 1;
        default:
            return 0;
    }
}

#if !defined(_WIN32) && !defined(_WIN64)

static string ConvertByVampire(const string& content, bool tptp) {

    int toPipe[2];
    int fromPipe[2];

    if (pipe(toPipe) == -1 || pipe(fromPipe) == -1) {
        perror("pipe");
        exit(130);
    }

    pid_t pid = fork();

    if (pid == -1) {
        perror("fork");
        exit(130);
    }

    if (pid == 0) {
        close(toPipe[1]);
        close(fromPipe[0]);

        dup2(toPipe[0], STDIN_FILENO);
        dup2(fromPipe[1], STDOUT_FILENO);

        execl("vampire",
              " --mode", "clausify",
              "-ep", "RSTC",
              "--input_syntax", tptp ? "tptp" : "smtlib2",
              nullptr);

        perror("execl");
        exit(130);
    }
    else {
        close(toPipe[0]);
        close(fromPipe[1]);

        if (write(toPipe[1], content.c_str(), content.size()) == -1) {
            perror("write");
            exit(130);
        }
        close(toPipe[1]);

        char buffer[4096] = { 0 };
        ssize_t bytesRead;
        string output;

        while ((bytesRead = read(fromPipe[0], buffer, sizeof(buffer))) > 0) {
            output.append(buffer, bytesRead);
        }

        close(fromPipe[0]);
        waitpid(pid, nullptr, 0);

        stringstream split(output);
        string line;
        stringstream ret;

        while (getline(split, line)) {
            if (!line.empty() && line[0] == '(')
                ret << line << '\n';
        }
        return ret.str();
    }
    exit(130);
}

#endif

static void deleteCNF(cnf<indexed_clause*>& root) {
    // delete literal as well -> avoid double freeing
    unordered_set<indexed_literal*> seen;
    for (unsigned i = 0; i < root.size(); i++) {
        for (const auto& l : root[i]->literals) {
            if (seen.insert(l).second)
                delete l;
        }
        delete root[i];
    }
}

void prep_rect(cnf<indexed_clause*>& matrix, ProgParams& progParams) {
    assert(progParams.mode == Rectangle || progParams.mode == Hybrid);
    for (int i = 0; i < matrix.size(); i++) {
        if (matrix[i]->ground) {
            progParams.multiplicity.push_back(1);
            continue;
        }
        progParams.multiplicity.push_back(progParams.depth);
    }
}

void prep_core(cnf<indexed_clause*>& matrix, ProgParams& progParams) {
    assert(progParams.mode == Core);
    for (int c = 0; c < matrix.size(); c++) {
        progParams.priority.push_back(0);
        if (matrix[c]->conjecture)
            progParams.multiplicity.push_back(1);
        else
            progParams.multiplicity.push_back(0);
    }
}

tri_state solve(const string& path, ProgParams& progParams, bool silent) {
    ifstream input(path);
    string content((istreambuf_iterator<char>(input)), istreambuf_iterator<char>());
    input.close();

    if (progParams.preprocess) {
#if !defined(_WIN32) && !defined(_WIN64)
        content = ConvertByVampire(content, progParams.format == TPTP);
#else
        cout << "Preprocessing is not supported on Windows" << endl;
        exit(130);
#endif
    }

    start_watch(overall_time);

    z3::context context;
    z3::expr_vector assertions(context);
    try {
        if (content.size() >= 3) {
            if (content[0] == -17 && content[1] == -69 && content[2] == -65) {
                content = content.substr(3); // Remove BOM
            }
        }
        assertions = context.parse_string(content.c_str());
    }
    catch (z3::exception& ex) {
        cout << "Failed to parse input file: " << ex.msg() << endl;
        return undef;
    }
    if (assertions.empty())
        return sat;
    complex_adt_solver* adtSolver = new complex_adt_solver();
    unsigned literalCnt = 0;
    cnf<indexed_clause*> cnf = to_cnf(mk_and(assertions), *adtSolver, literalCnt);

    vector<indexed_clause*> posClauses;
    vector<indexed_clause*> negClauses;
    posClauses.reserve(cnf.size());
    negClauses.reserve(cnf.size());

    unsigned conjectureCnt = 0;

    for (unsigned i = 0; i < cnf.size(); i++) {
        auto* clause = cnf[i];
        bool allPos = true;
        bool allNeg = true;
        conjectureCnt += (unsigned)clause->conjecture;
        for (const auto& lit : clause->literals) {
            if (allPos && !lit->polarity)
                allPos = false;
            if (allNeg && lit->polarity)
                allNeg = false;
            if (!allPos && !allNeg)
                break;
        }
        assert(!allPos || !allNeg);
        if (allPos)
            posClauses.push_back(clause);
        else if (allNeg)
            negClauses.push_back(clause);
    }
    if (posClauses.empty() || negClauses.empty()) {
        if (!silent)
            cout << "SAT because of polarity" << endl;
        deleteCNF(cnf);
        return sat;
    }

    auto smallestClauseSet = posClauses.size() < negClauses.size() ? posClauses : negClauses;

    if (progParams.conjectures == Auto)
        progParams.conjectures =
                conjectureCnt > 1 &&
                (unsigned)log2((double)conjectureCnt) > smallestClauseSet.size() ? Min : Keep;
    if (conjectureCnt == 0 && progParams.conjectures == Keep)
        progParams.conjectures = Min;

    assert(progParams.conjectures != Auto);

    std::vector<indexed_clause*> new_conj;

    if (progParams.conjectures == Pos)
        new_conj = std::move(posClauses);
    else if (progParams.conjectures == Neg)
        new_conj = std::move(negClauses);
    else if (progParams.conjectures == Min)
        new_conj = std::move(smallestClauseSet);
    else {
        assert(progParams.conjectures == Keep);
    }

    if (progParams.conjectures != Keep) {
        for (unsigned i = 0; i < cnf.size(); i++) {
            cnf[i]->conjecture = false;
        }
        for (auto* c : new_conj) {
            c->conjecture = true;
        }
    }

    assert(std::any_of(cnf.clauses.begin(), cnf.clauses.end(), [](const auto* x) { return x->conjecture; }));

    if (!silent) {
        cout << "Input file: " + path << "\n";
        cout << cnf.size() << " Clauses:\n";
        for (unsigned i = 0; i < cnf.size(); i++) {
            cout << "\tClause #" << i << ": " << cnf[i]->to_string() << (cnf[i]->conjecture ? "*" : "") << "\n";
        }
        std::flush(cout);
    }

    if (progParams.mode == Rectangle || progParams.mode == Hybrid) {
        prep_rect(cnf, progParams);
    }
    else {
        assert (progParams.mode == Core);
        prep_core(cnf, progParams);
    }

    if (progParams.checkProof)
        adtSolver->make_z3_adt(context);

    bool ground = true;
    for (unsigned i = 0; i < cnf.size(); i++) {
        if (!cnf[i]->ground) {
            ground = false;
            break;
        }
    }

    int64_t timeLeft = progParams.timeout == 0 ? INT_MAX : progParams.timeout;
    auto* propagator = new matrix_propagator(cnf, *adtSolver, progParams, literalCnt, (unsigned)timeLeft);

    for (unsigned id = progParams.depth; id < progParams.maxDepth; id++) {
        start_watch(level_time);
        // TODO
        // parameters.set("smt.restart_factor", 1.0);
        // parameters.set("random_seed", 1u);
        // parameters.set("timeout", (unsigned) timeLeft);
        // solver.set(parameters);

        tri_state res;
        try {
            propagator->assert_root();
            res = propagator->check();
        }
        catch (std::exception& ex) {
            cout << "Error: " << ex.what() << endl;
            exit(130);
        }

#ifdef DIMACS
        string dimacs = propagator->get_dimacs();
        ofstream out("output.dimacs");
        out << dimacs;
        out.close();
        std::cout << "Wrote dimacs output to output.dimacs" << std::endl;
#endif
#ifndef NDEBUG
        if (res == undef && propagator->is_smt()) {
            LogN("Reason unknow: " << propagator->get_z3_propagator()->get_solver().reason_unknown());
        }
#endif

        if (res != sat) {
            if (!silent)
                cout << "Failed with depth " << id << endl;
            timeLeft -= stop_watch(level_time);
            if (timeLeft <= 0) {
                if (!silent)
                    cout << "Timeout" << endl;
                deleteCNF(cnf);
                return undef;
            }
            if (id >= progParams.maxDepth) {
                if (!silent)
                    cout << "Reached depth limit" << endl;
                deleteCNF(cnf);
                return undef;
            }
            if (ground && id >= cnf.size()) {
                if (!silent)
                    cout << "SAT because of ground exhaustion" << endl;
                deleteCNF(cnf);
                delete propagator;
                return sat;
            }
            if (timeLeft < (unsigned)(1000 * 60 * 60 * 24))
                cout << "Time left: " << timeLeft << "ms" << endl;

            if (propagator->next_level()) {
                if (!silent)
                    cout << "SAT because of exhaustion" << endl;
                deleteCNF(cnf);
                delete propagator;
                return sat;
            }
            delete propagator;
            propagator = new matrix_propagator(cnf, *adtSolver, progParams, literalCnt, timeLeft);
            continue;
        }

        if (!silent)
            cout << "\nFound proof at level: " << id << endl;
        unordered_map<unsigned, int> usedClauses;
        unordered_map<term_instance*, string> prettyNames;

        if (silent) {
            deleteCNF(cnf);
            delete propagator;
            delete adtSolver;
            return unsat;
        }

        z3::solver subsolver(context);
        propagator->print_proof(prettyNames, usedClauses);

        auto sortedPrettyNames =
                to_sorted_vector(prettyNames,
                                 [](const pair<term_instance*, string>& a, const pair<term_instance*, string>& b) {
                                     if (a.first->t->FuncID > b.first->t->FuncID)
                                         return false;
                                     if (a.first->t->FuncID < b.first->t->FuncID)
                                         return true;
                                     if (a.first->cpy_idx() > b.first->cpy_idx())
                                         return false;
                                     if (a.first->cpy_idx() < b.first->cpy_idx())
                                         return true;
                                     return a.first->t->solver_id() > b.first->t->solver_id();
                                 });

        for (auto& s : sortedPrettyNames) {
            auto* interpretation = s.first->find_root(*propagator);
            if (interpretation != s.first)
                cout << "Substitution: " << s.second << " -> "
                     << interpretation->fully_expand(*propagator)->pretty_print(0, &prettyNames) << '\n';
        }

        cout << "Found proof in " << stop_watch(overall_time) << "ms" << endl;
        cout << "Time spend for connection reasoning: " << get_total_time(term_time) << "ms" << endl;
        cout << "               term reasoning:       " << get_total_time(connect_time) << "ms" << endl;
        cout << "               pb reasoning:         " << get_total_time(pb_time) << "ms" << endl;
        cout << "               tautology generation: " << get_total_time(tautology_time) << "ms" << endl;
        cout << "               var order generation: " << get_total_time(var_order_time) << "ms" << endl;
        cout << "               final reasoning:      " << get_total_time(final_time) << "ms" << endl;
        cout << "Final counts: " << propagator->get_final_cnt() << endl;
        cout << "Usage statistics:" << std::endl;
        std::vector<std::pair<unsigned, int>> sortedUsed = to_sorted_vector(usedClauses);
        for (auto& sorted : sortedUsed) {
            cout << "\tClause #" << sorted.first << ": " << sorted.second << endl;
        }
        vector<term_instance*> variables;
        variables.reserve(prettyNames.size());
        for (auto& entry : prettyNames) {
            variables.push_back(entry.first);
        }
        propagator->check_proof(context);
        deleteCNF(cnf);
        delete propagator;
        delete adtSolver;
        return unsat;
    }
    deleteCNF(cnf);
    delete propagator;
    delete adtSolver;
    return undef;
}

namespace std {
    template<>
    struct hash<vector<indexed_literal*>> {
        size_t operator()(const vector<indexed_literal*>& x) const {
            static const hash<indexed_literal> hash;
            size_t ret = 0;
            for (const auto& l : x) {
                ret += hash(*l) * 267193;
            }
            return ret;
        }
    };
}
namespace std {
    template<>
    struct equal_to<vector<indexed_literal*>> {
        bool operator()(const vector<indexed_literal*>& x, const vector<indexed_literal*>& y) const {
            if (x.size() != y.size())
                return false;
            for (unsigned i = 0; i < x.size(); i++) {
                if (*x[i] != *y[i])
                    return false;
            }
            return true;
        }
    };
}

cnf<indexed_clause*> to_cnf(const z3::expr& input, complex_adt_solver& adtSolver, unsigned& literalCnt) {
    z3::context& ctx = input.ctx();
    unordered_set<optional<z3::func_decl>> terms;
    z3::expr_vector scopeVariables(ctx);
    z3::sort_vector scopeSorts(ctx);
    z3::expr_vector substitutions(ctx);
    unordered_map<string, unsigned> nameCache;
    unordered_set<unsigned> visited;
    cnf<clause> cnf = to_cnf(ctx, input, true, scopeVariables, scopeSorts, substitutions, terms, nameCache, visited);

    unordered_map<z3::func_decl, term_abstraction> termAbstraction;

    bool finite = true;
    for (const auto& f : terms) {
        adtSolver.peek_term(f->range().name().str(), f->name().str(), (int)f->arity());
        finite &= f->arity() == 0;
    }

    for (unsigned i = 0; i < cnf.size(); i++) {
        for (const auto& variable : cnf[i].containedVars) {
            adtSolver.get_solver(
                    variable->get_sort().name().str()); // Include data types that occur without any constants/functions
        }
    }

    for (const auto& f : terms) {
        simple_adt_solver& solver = *adtSolver.get_solver(f->range().name().str());
        // We have to postpone this after the MkDatatypeSort
        termAbstraction.try_emplace(*f, &solver, solver.get_id(f->name().str()));
    }

    vector<indexed_clause*> newClauses;

    unordered_map<fo_literal, indexed_literal*> literalToIndexed;

    unsigned clauseIdx = 0;

    for (unsigned i = 0; i < cnf.size(); i++) {
        // Uninitialized, but we need the memory address before calling the constructor
        auto* nextPtr = (indexed_clause*)malloc(sizeof(indexed_clause));
        const auto& entry = cnf[i];
        vector<indexed_literal*> literals;
        z3::expr_vector from(ctx);
        for (const auto& var : entry.containedVars) {
            from.push_back(*var);
        }
        literals.reserve(entry.size());
        unordered_map<z3::func_decl, variable_abstraction> variableAbstraction;
        vector<term*> vars;
        vars.reserve(entry.containedVars.size());
        for (unsigned j = 0; j < entry.containedVars.size(); j++) {
            z3::func_decl arg = from[j].decl();
            auto& solver = *adtSolver.get_solver(arg.range().name().str());
            term* v = solver.make_var(arg.name().str(), nextPtr);
            vars.push_back(v);
            variableAbstraction.try_emplace(arg, &solver, v);
        }
        for (const auto& lit : entry.literals) {
            vector<const term*> args;
            args.reserve(lit.arg_bases.size());
            for (const auto& arg : lit.InitExprs.value()) {
                args.push_back(substitute_term(arg, termAbstraction, variableAbstraction));
            }
            fo_literal lit2(lit.name, lit.nameID, lit.polarity, args);
            indexed_literal* indexed;
            if (!tryGetValue(literalToIndexed, lit2, indexed)) {
                indexed = new indexed_literal(lit2, literalToIndexed.size());
                literalToIndexed.insert(make_pair(lit2, indexed));
            }
            literals.push_back(indexed);
        }

        sort(literals.begin(), literals.end(), [](auto o1, auto o2) { return o1->index < o2->index; });
        auto* cl = new(nextPtr) indexed_clause(clauseIdx++, literals, vars);
        cl->conjecture = entry.Conjecture;
        newClauses.push_back(cl);
    }

    literalCnt = literalToIndexed.size();
    return { std::move(newClauses) };
}

cnf<clause>
to_cnf(z3::context& ctx, const z3::expr& input, bool polarity, z3::expr_vector& scopeVars, z3::sort_vector& scopeSorts,
       z3::expr_vector& substitutions, unordered_set<optional<z3::func_decl>>& terms,
       unordered_map<string, unsigned>& nameCache,
       unordered_set<unsigned>& visited) {

    if (!eq(input.get_sort(), ctx.bool_sort()))
        throw solving_exception("Expected boolean expression");
    if (input.is_quantifier()) {
        bool isSkolem = input.is_exists() == polarity;
        unsigned prevSubstitutionsCnt = substitutions.size();
        unsigned boundCnt = Z3_get_quantifier_num_bound(ctx, input);

        cnf<clause> res;
        if (isSkolem) {
            cout << "Info for production: Vampire should have removed existential quantifier" << std::endl;
            const auto& vars = scopeVars;
            const auto& sorts = scopeSorts;

            for (unsigned i = 0; i < boundCnt; i++) {
                z3::func_decl skolem = fresh_function(
                        ctx,
                        "sk_" + z3::symbol(ctx, Z3_get_quantifier_bound_name(ctx, input, i)).str(),
                        sorts,
                        z3::sort(ctx, Z3_get_quantifier_bound_sort(ctx, input, i))
                );
                substitutions.push_back(skolem(vars));
                terms.insert(make_optional(skolem));
            }
            res = to_cnf(ctx, input.body(), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
            substitutions.resize(prevSubstitutionsCnt);
            return res;
        }
        assert(scopeVars.size() == scopeSorts.size());
        unsigned scopeCnt = scopeVars.size();

        for (unsigned i = 0; i < boundCnt; i++) {
            z3::sort s(ctx, Z3_get_quantifier_bound_sort(ctx, input, i));
            z3::expr e = fresh_constant(
                    ctx,
                    z3::symbol(ctx, Z3_get_quantifier_bound_name(ctx, input, i)).str(),
                    s
            );
            substitutions.push_back(e);
            scopeVars.push_back(e);
            scopeSorts.push_back(s);
        }
        res = to_cnf(ctx, input.body(), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        substitutions.resize(prevSubstitutionsCnt);
        scopeVars.resize(scopeCnt);
        scopeSorts.resize(scopeCnt);
        return res;
    }

    auto decl = input.decl();
    switch (decl.decl_kind()) {
        case Z3_OP_UNINTERPRETED: {
            cnf<clause> c;
            if (decl.arity() == 1 && decl.name().str() == "#") {
                c = to_cnf(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                           visited);
                vector<clause> clauses;
                clauses.reserve(c.size());
                add_range(clauses, c.clauses);
                for (auto& clause : clauses) {
                    clause.Conjecture = true;
                }
                return { clauses };
            }
            for (const auto& arg : input.args()) {
                CollectTerm(arg, terms, visited);
            }
            z3::expr cpy = input;
            z3::expr atom = cpy.substitute(reverse(substitutions));
            if (!polarity)
                atom = !atom;
            z3::expr_vector v(ctx);
            v.push_back(atom);
            c = cnf<clause>({ clause(v, nameCache) });
            c[0].AddVariables(scopeVars);
            return c;
        }
        case Z3_OP_NOT:
            return to_cnf(ctx, input.arg(0), !polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                          visited);
        case Z3_OP_AND:
            switch (input.num_args()) {
                case 0:
                    return cnf<clause>::get_true();
                case 1:
                    return to_cnf(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                                  visited);
                default: {
                    vector<cnf<clause>> cnfs;
                    unsigned sz = input.num_args();
                    cnfs.reserve(sz);
                    for (unsigned i = 0; i < sz; i++) {
                        cnfs.push_back(to_cnf(ctx, input.arg(i), polarity, scopeVars, scopeSorts, substitutions,
                                              terms, nameCache, visited));
                    }
                    return { cnfs };
                }
            }
        case Z3_OP_OR:
            switch (input.num_args()) {
                case 0:
                    return cnf<clause>::get_false();
                case 1:
                    return to_cnf(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                                  visited);
                default: {
                    z3::expr arg1(ctx);
                    z3::expr arg2 = input.arg(input.num_args() - 1);
                    if (input.num_args() == 2)
                        arg1 = input.arg(0);
                    else {
                        z3::expr_vector args = input.args();
                        args.resize(args.size() - 1);
                        arg1 = mk_or(args);
                    }

                    auto cnf1 = to_cnf(ctx, arg1, polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                                       visited);
                    auto cnf2 = to_cnf(ctx, arg2, polarity, scopeVars, scopeSorts, substitutions, terms, nameCache,
                                       visited);
                    vector<clause> clauses;
                    clauses.reserve((unsigned)cnf1.size() * (unsigned)cnf2.size());
                    for (int i = 0; i < cnf1.size(); i++) {
                        auto e1 = cnf1[i];
                        for (int j = 0; j < cnf2.size(); j++) {
                            auto e2 = cnf2[i];
                            clauses.emplace_back(e1, e2);
                            clauses.back().Conjecture = e1.Conjecture | e2.Conjecture;
                        }
                    }
                    return { clauses };
                }
            }
        case Z3_OP_IMPLIES:
            return to_cnf(ctx, !input.arg(0) || input.arg(1), polarity,
                          scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        case Z3_OP_EQ:
            return to_cnf(ctx,
                          (input.arg(0) || !input.arg(1)) && (!input.arg(0) || input.arg(1)),
                          polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        default:
            throw solving_exception("Unexpected operator " + input.decl().name().str());
    }
}

void CollectTerm(const z3::expr& expr, unordered_set<optional<z3::func_decl>>& language,
                 unordered_set<unsigned>& visited) {
    if (expr.is_var())
        return;
    if (!visited.insert(expr.id()).second)
        return;
    if (expr.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        language.insert(expr.decl());
    for (const auto& arg : expr.args())
        CollectTerm(arg, language, visited);
}

const term* substitute_term(const z3::expr& expr,
                      const unordered_map<z3::func_decl, term_abstraction>& termAbstraction,
                      const unordered_map<z3::func_decl, variable_abstraction>& varAbstraction) {
    vector<const term*> args;
    args.reserve(expr.num_args());
    for (const auto& arg : expr.args())
        args.push_back(substitute_term(arg, termAbstraction, varAbstraction));
    z3::func_decl decl = expr.decl();
    term_abstraction abstraction;
    return tryGetValue(termAbstraction, decl, abstraction)
           ? abstraction.apply(args)
           : varAbstraction.at(decl).apply(args);
}
