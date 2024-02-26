#pragma once

#include <climits>
#include <vector>

enum InputFormat {
    TPTP,
    SMTLIB,
};


enum IncStrategy {
    Core,
    Rectangle,
};

enum ConjStrategy {
    Auto,
    Keep,
    Pos,
    Neg,
    Min,
};

struct ProgParams {
    int Timeout = 0;
    IncStrategy Mode = Rectangle;
    unsigned Depth = 1;
    unsigned MaxDepth = UINT_MAX;
    bool ExternalIteration = true;
    bool Test = false;
    bool Preprocess = true;
    bool CheckProof = false;
    ConjStrategy Conjectures = Auto;
    // bool NewCore;
    bool Z3Split = false;
    InputFormat Format = TPTP;

    std::vector<unsigned> multiplicity;
    std::vector<unsigned> priority;

#if defined(_WIN32) || defined(_WIN64)

    ProgParams() {
        Format = SMTLIB;
        Preprocess = false;
    }

#else
    ProgParams() = default;
#endif
};

void ParseParams(int argc, char* argv[], ProgParams& progParams);
