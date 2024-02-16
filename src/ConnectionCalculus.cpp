#include "ConnectionCalculus.h"
#include "CLIParser.h"
#include "Clause.h"
#include "CNF.h"
#include "utils.h"
#include "ADTSolver.h"
#include "matrix_propagator.h"
#include <fstream>
#include <z3++.h>

#if !defined(_WIN32) && !defined(_WIN64)

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#endif

Term* VariableAbstraction::Apply(const pvector<Term>& args) const {
    assert(args.empty());
    Term* t = solver->MakeVar(-id - 1);
    return t;
}

Term* TermAbstraction::Apply(const pvector<Term>& args) const {
    Term* t = solver->MakeTerm(termId, args);
    return t;
}

int main(int argc, char* argv[]) {

    ProgParams progParams;
    ParseParams(argc, argv, progParams);
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
    } else {
        close(toPipe[0]);
        close(fromPipe[1]);

        write(toPipe[1], content.c_str(), content.size());
        close(toPipe[1]);

        char buffer[4096];
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

static void deleteCNF(CNF<IndexedClause*>& root) {
    // delete literal as well -> avoid double freeing
    unordered_set<IndexedLiteral*> seen;
    for (auto& c : root.nonConjectureClauses) {
        for (const auto& l : c->literals) {
            if (seen.insert(l).second)
                delete l;
        }
        delete c;
    }
    for (auto& c : root.conjectureClauses) {
        for (const auto& l : c->literals) {
            if (seen.insert(l).second)
                delete l;
        }
        delete c;
    }
}

tri_state solve(const string& path, ProgParams& progParams, bool silent) {
    ifstream input(path);
    string content((istreambuf_iterator<char>(input)), istreambuf_iterator<char>());
    input.close();

    if (progParams.Preprocess) {
#if !defined(_WIN32) && !defined(_WIN64)
        content = ConvertByVampire(content, progParams.Format == TPTP);
#else
        cout << "Preprocessing is not supported on Windows" << endl;
        exit(130);
#endif
    }

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
    ComplexADTSolver adtSolver(progParams.Z3Split);
    unsigned literalCnt = 0;
    auto cnf = ToCNF(mk_and(assertions), adtSolver, literalCnt);

    if (!silent) {
        cout << "Input file: " + path << "\n";
        cout << cnf.size() << " Clauses:\n";
        for (unsigned i = 0; i < cnf.size(); i++) {
            cout << "\tClause #" << i << ": " << cnf[i]->ToString() << (cnf.IsConjecture(i) ? "*" : "") << "\n";
        }
        std::flush(cout);
    }

    int timeLeft = progParams.Timeout == 0 ? INT_MAX : progParams.Timeout;
    matrix_propagator propagator(cnf, adtSolver, progParams, literalCnt);

    for (unsigned id = progParams.StartDepth; id < progParams.MaxDepth; id++) {
        start_watch();
        // TODO
        // parameters.set("smt.restart_factor", 1.0);
        // parameters.set("random_seed", 1u);
        // parameters.set("timeout", (unsigned) timeLeft);
        // solver.set(parameters);

        tri_state res;
        try {
            propagator.Running = true;
            propagator.AssertRoot();
            res = propagator.Satisfiable ? sat : propagator.check();
        }
        catch (std::exception& ex) {
            cout << "Error: " << ex.what() << endl;
            exit(130);
        }
        propagator.Running = false;

        if (res != sat) {
            if (!silent)
                cout << "Failed with depth " << id << "\n" << endl;
            timeLeft -= (int) stop_watch();
            if (timeLeft <= 0) {
                if (!silent)
                    cout << "Timeout" << endl;
                deleteCNF(cnf);
                return undef;
            }
            if (id >= progParams.MaxDepth) {
                if (!silent)
                    cout << "Reached depth limit" << endl;
                deleteCNF(cnf);
                return undef;
            }
            if (timeLeft < 1000 * 60 * 60 * 24)
                cout << "Time left: " << timeLeft << "ms" << endl;
            propagator.solver->reset_constraint();
            propagator.next_level();
            continue;
        }
        if (propagator.Satisfiable) {
            if (!silent)
                cout << "SAT because of polarity" << endl;
            deleteCNF(cnf);
            return sat;
        }

        if (!silent)
            cout << "\nFound proof at level: " << id << endl;
        unordered_map<unsigned, int> usedClauses;
        unordered_map<variableIdentifier, string> prettyNames;

        if (silent) {
            deleteCNF(cnf);
            return unsat;
        }

        z3::solver subsolver(context);
        propagator.PrintProof(subsolver, prettyNames, usedClauses);

        auto sortedPrettyNames = to_sorted_vector(prettyNames,
                                                  [](auto& a, const auto& b) {
                                                      if (a.first.id > b.first.id)
                                                          return false;
                                                      if (a.first.id < b.first.id)
                                                          return true;
                                                      if (a.first.cpyIdx > b.first.cpyIdx)
                                                          return false;
                                                      if (a.first.cpyIdx < b.first.cpyIdx)
                                                          return true;
                                                      return a.first.solverId < b.first.solverId;
                                                  });

        for (auto& s: sortedPrettyNames) {
            auto interpretation = adtSolver.Solvers[s.first.solverId]->GetModel(s.first.id, s.first.cpyIdx);
            if (!interpretation.has_value())
                continue;
            cout << "Substitution: " << s.second << " -> "
                 << interpretation->term->PrettyPrint(interpretation->cpyIdx, &prettyNames) << '\n';
        }

        cout << "Usage statistics:" << std::endl;
        std::vector<std::pair<unsigned, int>> sortedUsed = to_sorted_vector(usedClauses);
        for (auto& sorted: sortedUsed) {
            cout << "\tClause #" << sorted.first << ": " << sorted.second << endl;
        }
        deleteCNF(cnf);
        return unsat;
    }
    deleteCNF(cnf);
    return undef;
}

namespace std {
    template<>
    struct hash<pvector<IndexedLiteral>> {
        size_t operator()(const pvector<IndexedLiteral>& x) const {
            static const hash<IndexedLiteral> hash;
            size_t ret = 0;
            for (const auto& l: x) {
                ret += hash(*l) * 267193;
            }
            return ret;
        }
    };
}
namespace std {
    template<>
    struct equal_to<pvector<IndexedLiteral>> {
        bool operator()(const pvector<IndexedLiteral>& x, const pvector<IndexedLiteral>& y) const {
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

CNF<IndexedClause*> ToCNF(const z3::expr& input, ComplexADTSolver& adtSolver, unsigned& literalCnt) {
    z3::context& ctx = input.ctx();
    unordered_set<optional<z3::func_decl>> terms;
    z3::expr_vector scopeVariables(ctx);
    z3::sort_vector scopeSorts(ctx);
    z3::expr_vector substitutions(ctx);
    unordered_map<string, unsigned> nameCache;
    unordered_set<unsigned> visited;
    CNF<Clause> cnf = ToCNF(ctx, input, true, scopeVariables, scopeSorts, substitutions, terms, nameCache, visited);

    unordered_map<z3::func_decl, TermAbstraction> termAbstraction;

    bool finite = true;
    for (const auto& f: terms) {
        adtSolver.PeekTerm(f->range().name().str(), f->name().str(), (int) f->arity());
        finite &= f->arity() == 0;
    }

    for (unsigned i = 0; i < cnf.size(); i++) {
        for (auto& variable: cnf[i].containedVars) {
            adtSolver.GetSolver(
                    variable->get_sort().name().str()); // Include data types that occur without any constants/functions
        }
    }

    // For finite domains having a custom solver does not give us much ==> better take the debugged Z3 solver
    adtSolver.MakeZ3ADT(ctx);

    for (const auto& f: terms) {
        SimpleADTSolver& solver = *adtSolver.GetSolver(f->range().name().str());
        // We have to postpone this after the MkDatatypeSort
        termAbstraction.try_emplace(*f, &solver, solver.GetId(f->name().str()));
    }

    pvector<IndexedClause> newNonConjectureClauses;
    pvector<IndexedClause> newConjectureClauses;

    unordered_map<Literal, IndexedLiteral*> literalToIndexed;
    unordered_set<pvector<IndexedLiteral>> clauses;//(OrderedArrayComparer<IndexedLiteral>());

    unsigned clauseIdx = 0;

    for (unsigned i = 0; i < cnf.size(); i++) {
        const auto& entry = cnf[i];
        pvector<IndexedLiteral> literals;
        z3::expr_vector from(ctx);
        for (const auto& var: entry.containedVars) {
            from.push_back(*var);
        }
        literals.reserve(entry.size());
        unordered_map<z3::func_decl, VariableAbstraction> variableAbstraction;
        for (int j = 0; j < entry.containedVars.size(); j++) {
            z3::func_decl arg = from[j].decl();
            auto& solver = *adtSolver.GetSolver(arg.range().name().str());
            variableAbstraction.try_emplace(
                    arg,
                    &solver,
                    solver.MakeVar(arg.name().str()));
        }
        for (const auto& lit: entry.literals) {
            pvector<Term> args;
            args.reserve(lit.ArgBases.size());
            for (const auto& arg: lit.InitExprs.value()) {
                args.push_back(SubstituteTerm(arg, termAbstraction, variableAbstraction));
            }
            Literal lit2(lit.name, lit.nameID, lit.polarity, args);
            IndexedLiteral* indexed;
            if (!tryGetValue(literalToIndexed, lit2, indexed)) {
                indexed = new IndexedLiteral(lit2, literalToIndexed.size());
                literalToIndexed.insert(make_pair(lit2, indexed));
            }
            literals.push_back(indexed);
        }

        sort(literals.begin(), literals.end(), [](auto o1, auto o2) { return o1->Index < o2->Index; });
        // TODO: Check subset
        if (!clauses.insert(literals).second) {
            // Eliminate duplicate clauses
            continue;
        }
        pvector<IndexedClause>& list = cnf.IsConjecture(i) ? newConjectureClauses : newNonConjectureClauses;
        z3::sort_vector sorts(ctx);
        sorts.resize(from.size());
        for (unsigned j = 0; j < sorts.size(); j++) {
            z3::sort s = adtSolver.GetZ3Sort(from[j].get_sort().name().str());
            sorts.set(j, s);
        }
        list.push_back(new IndexedClause(clauseIdx++, literals, sorts));
    }

    literalCnt = literalToIndexed.size();
    return { std::move(newNonConjectureClauses), std::move(newConjectureClauses) };
}

CNF<Clause> ToCNF(z3::context& ctx, const z3::expr& input, bool polarity, z3::expr_vector& scopeVars, z3::sort_vector& scopeSorts,
      z3::expr_vector& substitutions, unordered_set<optional<z3::func_decl>>& terms, unordered_map<string, unsigned>& nameCache,
      unordered_set<unsigned>& visited) {

    if (!eq(input.get_sort(), ctx.bool_sort()))
        throw solving_exception("Expected boolean expression");
    if (input.is_quantifier()) {
        bool isSkolem = input.is_exists() == polarity;
        unsigned prevSubstitutionsCnt = substitutions.size();
        unsigned boundCnt = Z3_get_quantifier_num_bound(ctx, input);

        CNF<Clause> res;
        if (isSkolem) {
            cout << "Info for production: Vampire should have removed existential quantifier" << std::endl;
            const auto& vars = scopeVars;
            const auto& sorts = scopeSorts;

            for (unsigned i = 0; i < boundCnt; i++) {
                z3::func_decl skolem = FreshFunction(
                        ctx,
                        "sk_" + z3::symbol(ctx, Z3_get_quantifier_bound_name(ctx, input, i)).str(),
                        sorts,
                        z3::sort(ctx, Z3_get_quantifier_bound_sort(ctx, input, i))
                );
                substitutions.push_back(skolem(vars));
                terms.insert(make_optional(skolem));
            }
            res = ToCNF(ctx, input.body(), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
            substitutions.resize(prevSubstitutionsCnt);
            return res;
        }
        assert(scopeVars.size() == scopeSorts.size());
        unsigned scopeCnt = scopeVars.size();

        for (unsigned i = 0; i < boundCnt; i++) {
            z3::sort s(ctx, Z3_get_quantifier_bound_sort(ctx, input, i));
            z3::expr e = FreshConstant(
                    ctx,
                    z3::symbol(ctx, Z3_get_quantifier_bound_name(ctx, input, i)).str(),
                    s
            );
            substitutions.push_back(e);
            scopeVars.push_back(e);
            scopeSorts.push_back(s);
        }
        res = ToCNF(ctx, input.body(), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        substitutions.resize(prevSubstitutionsCnt);
        scopeVars.resize(scopeCnt);
        scopeSorts.resize(scopeCnt);
        return res;
    }

    auto decl = input.decl();
    switch (decl.decl_kind()) {
        case Z3_OP_UNINTERPRETED: {
            CNF<Clause> cnf;
            if (decl.arity() == 1 && decl.name().str() == "#") {
                cnf = ToCNF(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
                vector<Clause> clauses;
                clauses.reserve(cnf.nonConjectureClauses.size() + cnf.conjectureClauses.size());
                add_range(clauses, cnf.nonConjectureClauses);
                add_range(clauses, cnf.conjectureClauses);
                return {vector<Clause>(), clauses};
            }
            for (const auto& arg: input.args()) {
                CollectTerm(arg, terms, visited);
            }
            z3::expr cpy = input;
            z3::expr atom = cpy.substitute(Reverse(substitutions));
            if (!polarity)
                atom = !atom;
            z3::expr_vector v(ctx);
            v.push_back(atom);
            cnf = CNF<Clause>({Clause(v, nameCache)});
            cnf[0].AddVariables(scopeVars);
            return cnf;
        }
        case Z3_OP_NOT:
            return ToCNF(ctx, input.arg(0), !polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        case Z3_OP_AND:
            switch (input.num_args()) {
                case 0:
                    return CNF<Clause>::GetTrue()   ;
                case 1:
                    return ToCNF(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
                default: {
                    vector<CNF<Clause>> cnfs;
                    unsigned sz = input.num_args();
                    cnfs.reserve(sz);
                    for (unsigned i = 0; i < sz; i++) {
                        cnfs.push_back(ToCNF(ctx, input.arg(i), polarity, scopeVars, scopeSorts, substitutions,
                                        terms, nameCache, visited));
                    }
                    return {cnfs};
                }
            }
        case Z3_OP_OR:
            switch (input.num_args()) {
                case 0:
                    return CNF<Clause>::GetFalse();
                case 1:
                    return ToCNF(ctx, input.arg(0), polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
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

                    auto cnf1 = ToCNF(ctx, arg1, polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
                    auto cnf2 = ToCNF(ctx, arg2, polarity, scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
                    vector<Clause> clauses;
                    clauses.reserve(cnf1.size() * cnf2.size());
                    for (int i = 0; i < cnf1.size(); i++) {
                        auto e1 = cnf1[i];
                        for (int j = 0; j < cnf2.size(); j++) {
                            auto e2 = cnf2[i];
                            clauses.emplace_back(e1, e2);
                        }
                    }
                    return {clauses};
                }
            }
        case Z3_OP_IMPLIES:
            return ToCNF(ctx, !input.arg(0) || input.arg(1), polarity,
                         scopeVars, scopeSorts, substitutions, terms, nameCache, visited);
        case Z3_OP_EQ:
            return ToCNF(ctx,
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
    for (const auto& arg: expr.args())
        CollectTerm(arg, language, visited);
}

Term* SubstituteTerm(const z3::expr& expr,
                     const unordered_map<z3::func_decl, TermAbstraction>& termAbstraction,
                     const unordered_map<z3::func_decl, VariableAbstraction>& varAbstraction) {
    vector<Term*> args;
    args.reserve(expr.num_args());
    for (const auto& arg: expr.args())
        args.push_back(SubstituteTerm(arg, termAbstraction, varAbstraction));
    z3::func_decl decl = expr.decl();
    TermAbstraction abstraction;
    return tryGetValue(termAbstraction, decl, abstraction)
        ? abstraction.Apply(args)
        : varAbstraction.at(decl).Apply(args);
}
