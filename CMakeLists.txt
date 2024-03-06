cmake_minimum_required(VERSION 3.16.3)
project (UPCoP)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(FORCE_NDEBUG "Force NDEBUG" OFF)
option(Z3_HEADER "Path to Z3 headers" "")
option(CADICAL_HEADER "Path to Cadical headers" "")
option(Z3_LIB "Path to Z3 library" "")
option(CADICAL_LIB "Path to Cadical library" "")
option(NOLOG "Don't output log" "")

if ((NOT Z3_HEADER) OR (NOT Z3_LIB))
    message(FATAL_ERROR "Did not find Z3. Pass path directly to CMake via -D")
    fail()
endif()
if ((NOT CADICAL_HEADER) OR (NOT CADICAL_LIB))
    message(FATAL_ERROR "Did not find CaDiCal. Pass path directly to CMake via -D")
    fail()
endif()

include_directories(${CADICAL_HEADER})
include_directories(${Z3_HEADER})

add_subdirectory(src)
