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
    int timeout = 0;
    IncStrategy mode = Rectangle;
    unsigned depth = 1;
    unsigned maxDepth = UINT_MAX;
    bool preprocess = true;
    bool checkProof = false;
    bool smt = false;
    ConjStrategy conjectures = Keep;
    bool satSplit = true; // TODO: For now let's fix it
    InputFormat format = TPTP;

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
