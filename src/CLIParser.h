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
    Hybrid,
};

enum ConjStrategy : unsigned char {
    Auto,
    Keep,
    Pos,
    Neg,
    Min,
};

struct ProgParams {
    int timeout = 0;
    IncStrategy mode = Rectangle;
    unsigned depth = 1;
    unsigned maxDepth = UINT_MAX;
    bool preprocess = false;
    bool checkProof = false;
    bool smt = false;
    ConjStrategy conjectures = Keep;
    bool satSplit = true; // TODO: For now let's fix it
    InputFormat format = SMTLIB;

    std::vector<unsigned> multiplicity;
    std::vector<unsigned> priority;

#if defined(_WIN32) || defined(_WIN64)

    ProgParams() {
        format = SMTLIB;
        preprocess = false;
    }

#else
    ProgParams() = default;
#endif
};

void parse_params(int argc, char* argv[], ProgParams& progParams);
