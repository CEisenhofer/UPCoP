#include "CLIParser.h"
#include "utils.h"
#include <iostream>
#include <filesystem>

static void CrashParams(const std::string& error) {
    if (!error.empty())
        std::cout << "Error: " << error << '\n';
    std::cout
            << "Usage: ConnectionCalculus [-d initial_depth] [-dm max_depth] [-t timeout : ms] [-m [core|rect] [--input_syntax [tptp|smtlib]] [--no-preprocess] [--preprocess] [--conj] [-c [auto|keep|pos|neg|min]] [--split] [--sat] [--smt] [--check] path-to-smt2"
            << std::endl;
    exit(-1);
}

void parse_params(int argc, char* argv[], ProgParams& progParams) {
    int i = 1;
    while (i < argc) {
        if (i == argc - 1)
            break;

        std::string c = argv[i];
        std::string current = to_lower(c);

        if (c == "-t" || current == "--timeout") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_int(argv[i + 1], progParams.timeout))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.timeout < 0)
                CrashParams("Negative timeout");
            i += 2;
            continue;
        }
        if (c == "-d" || current == "--depth") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_uint(argv[i + 1], progParams.depth))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.depth == 0)
                progParams.depth = 1;
            i += 2;
            continue;
        }
        if (c == "-dm" || current == "--lim" || current == "--limit") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            if (!to_uint(argv[i + 1], progParams.maxDepth))
                CrashParams("No number: " + std::string(argv[i + 1]));
            if (progParams.maxDepth == 0)
                progParams.maxDepth = UINT_MAX;
            i += 2;
            continue;
        }
        if (current == "--input_syntax") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            std::string next = to_lower(argv[i + 1]);
            if (next == "tptp")
                progParams.format = TPTP;
            else if (next == "smtlib" || next == "smtlib2")
                progParams.format = SMTLIB;
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
                progParams.mode = Rectangle;
            else if (next == "core")
                progParams.mode = Core;
            else if (next == "hybrid")
                progParams.mode = Hybrid;
            else
                CrashParams("Unknown mode: " + std::string(argv[i + 1]));
            i += 2;
            continue;
        }

        if (current == "--split") {
            progParams.satSplit = true;
            i++;
            continue;
        }
        if (current == "--check") {
            progParams.checkProof = true;
            i++;
            continue;
        }
        if (current == "--sat") {
            progParams.smt = false;
            i++;
            continue;
        }
        if (current == "--smt") {
            progParams.smt = true;
            i++;
            continue;
        }
        if (current == "--no-preprocess") {
            progParams.preprocess = false;
            progParams.format = SMTLIB;
            i++;
            continue;
        }
        if (current == "--preprocess") {
            progParams.preprocess = true;
            i++;
            continue;
        }

        if (current == "--conj") {
            progParams.conjectures = Keep;
            i++;
            continue;
        }
        if (c == "-c") {
            if (i + 1 >= argc)
                CrashParams("Missing argument for " + c);
            std::string next = to_lower(argv[i + 1]);
            if (next == "auto")
                progParams.conjectures = Auto;
            else if (next == "keep")
                progParams.conjectures = Keep;
            else if (next == "pos")
                progParams.conjectures = Pos;
            else if (next == "neg")
                progParams.conjectures = Neg;
            else if (next == "min")
                progParams.conjectures = Min;
            else
                CrashParams("Unknown conjecture mode: " + std::string(argv[i + 1]));
            i += 2;
            continue;
        }
        CrashParams("Unknown argument: " + c);
    }

    if (progParams.maxDepth < progParams.depth)
        CrashParams("Maximum depth has to be at least as high as the starting depth");
    if (!progParams.preprocess && progParams.format == TPTP)
        CrashParams("TPTP input is only supported with preprocessing");
    if (argc < 2 || !std::filesystem::exists(argv[argc - 1]))
        CrashParams("File " + std::string(argv[argc - 1]) + " does not exist");
    if (progParams.depth > 1)
        std::cout << "Warning: Did not start with level 1. Run might be incomplete (unlikely but possible)" << std::endl;
}
