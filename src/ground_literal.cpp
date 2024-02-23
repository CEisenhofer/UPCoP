#include "propagator_base.h"

string ground_literal::ToString() const {
    return propagator_base::PrettyPrintLiteral(*this, nullptr);
}

