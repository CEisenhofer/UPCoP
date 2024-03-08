#include "propagator_base.h"

#ifndef NDEBUG
string ground_literal::to_string() const {
    return propagator_base::pretty_print_literal(*this, nullptr);
}
#endif

