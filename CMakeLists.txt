cmake_minimum_required(VERSION 3.16.3)
project (UPCoP)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(FORCE_NDEBUG "Force NDEBUG" OFF)
option(Z3_INCLUDE_DIR "Path to Z3 headers" "")
option(CADICAL_HEADER "Path to Cadical headers" "")
option(Z3_LIBRARIES "Path to Z3 library" "")
option(CADICAL_LIB "Path to Cadical library" "")

if ((NOT Z3_INCLUDE_DIR) OR (NOT Z3_LIBRARIES))
    message(FATAL_ERROR "Did not find Z3. Pass path directly to CMake via -D")
    fail()
endif()
if ((NOT CADICAL_INCLUDE_DIR) OR (NOT CADICAL_LIBRARIES))
    message(FATAL_ERROR "Did not find CaDiCal. Pass path directly to CMake via -D")
    fail()
endif()

include_directories(${CADICAL_INCLUDE_DIR})
include_directories(${Z3_INCLUDE_DIR})

add_subdirectory(src)
