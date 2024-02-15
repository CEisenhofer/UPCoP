#include "CLIParser.h"
#include "utils.h"
#include <filesystem>

static void CrashParams(const std::string& error) {
    if (!error.empty())
        std::cout << "Error: " << error << '\n';
    std::cout
            << "Usage: ConnectionCalculus [-d initial_depth] [-dm max_depth] [-t timeout : ms] [-m [core|rect] [--input_syntax [tptp|smtlib]] [--no-preprocess] [--preprocess] [--conj] [-c [auto|keep|pos|neg|min]] [--split] [--check] path-to-smt2"
            << std::endl;
    exit(-1);
}

void ParseParams(int argc, char* argv[], ProgParams& progParams) {
    int i = 1;
    while (i < argc) {
        if (i == argc - 1)
            break;

        std::string c = argv[i];
        std::string current = to_lower(c);

        if (current == "--test") {
            progParams.Test = true;
            i++;
            continue;
        }
        if (c == "-t" || current == "--timeout") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_int(argv[i + 1], progParams.Timeout))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.Timeout < 0)
                CrashParams("Negative timeout");
            i += 2;
            continue;
        }
        if (c == "-d" || current == "--depth") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_uint(argv[i + 1], progParams.StartDepth))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.StartDepth == 0)
                progParams.StartDepth = 1;
            i += 2;
            continue;
        }
        if (c == "-dm" || current == "--lim" || current == "--limit") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_uint(argv[i + 1], progParams.MaxDepth))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.MaxDepth == 0)
                progParams.MaxDepth = UINT_MAX;
            i += 2;
            continue;
        }
        if (current == "--input_syntax") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            std::string next = to_lower(argv[i + 1]);
            if (next == "tptp")
                progParams.Format = TPTP;
            else if (next == "smtlib" || next == "smtlib2")
                progParams.Format = SMTLIB;
            else
                CrashParams("Unknown input syntax: " + std::string(argv[i + 1]));
            i += 2;
            continue;
        }

        if (c == "-m") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            std::string next = to_lower(argv[i + 1]);
            if (next == "rect")
                progParams.Mode = Rectangle;
            else if (next == "core")
                progParams.Mode = Core;
            else
                CrashParams("Unknown mode: " + std::string(argv[i + 1]));
            i += 2;
            continue;
        }

        if (current == "--split") {
            progParams.Z3Split = true;
            i++;
            continue;
        }
        if (current == "--check") {
            progParams.CheckProof = true;
            i++;
            continue;
        }
        if (current == "--no-preprocess") {
            progParams.Preprocess = false;
            progParams.Format = SMTLIB;
            i++;
            continue;
        }
        if (current == "--preprocess") {
            progParams.Preprocess = true;
            i++;
            continue;
        }

        if (current == "--conj") {
            progParams.Conjectures = Keep;
            i++;
            continue;
        }
        if (c == "-c") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            std::string next = to_lower(argv[i + 1]);
            if (next == "auto")
                progParams.Conjectures = Auto;
            else if (next == "keep")
                progParams.Conjectures = Keep;
            else if (next == "pos")
                progParams.Conjectures = Pos;
            else if (next == "neg")
                progParams.Conjectures = Neg;
            else if (next == "min")
                progParams.Conjectures = Min;
            else
                CrashParams("Unknown conjecture mode: " + std::string(argv[i + 1]));
            i += 2;
            continue;
        }
        CrashParams("Unknown argument: " + c);
    }

    if (progParams.MaxDepth < progParams.StartDepth)
        CrashParams("Maximum depth has to be at least as high as the starting depth");
    if (!progParams.Preprocess && progParams.Format == TPTP)
        CrashParams("TPTP input is only supported with preprocessing");
    if (!progParams.Test && argc < 1)
        CrashParams("No file given");
    if (!progParams.Test && (argc < 2 || !std::filesystem::exists(argv[argc - 1])))
        CrashParams("File " + std::string(argv[argc - 1]) + " does not exist");
    if (progParams.StartDepth > 1)
        std::cout << "Warning: Did not start with level 1. Run might be incomplete (unlikely but possible)" << std::endl;
}
