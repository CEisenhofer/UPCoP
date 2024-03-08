#pragma once

#include <climits>
#include <vector>

enum InputFormat : unsigned char {
    TPTP,
    SMTLIB,
};


enum IncStrategy : unsigned char {
    Core,
    Rectangle,
};

enum ConjStrategy : unsigned char {
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
    bool Preprocess = true;
    bool CheckProof = false;
    ConjStrategy Conjectures = Keep;
    bool SATSplit = false;
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

void parse_params(int argc, char* argv[], ProgParams& progParams);
