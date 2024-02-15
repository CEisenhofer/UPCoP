#include "PropagatorBase.h"

string GroundLiteral::ToString() const {
    return PropagatorBase::PrettyPrintLiteral(*this, nullptr);
}

