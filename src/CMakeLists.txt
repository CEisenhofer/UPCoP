cmake_minimum_required(VERSION 3.16.3)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

if (CMAKE_BUILD_TYPE MATCHES Debug)
    message(STATUS "Debug build")
    if (MSVC)
        add_definitions("/Ob0")
    else ()
        add_definitions("-fno-inline")
        add_definitions("-O0")
    endif ()
elseif (CMAKE_BUILD_TYPE MATCHES Release)
    message(STATUS "Release build")
endif ()

if (NOLOG)
    add_definitions(-DNOLOG)
    message(STATUS "Manually disabled logging in debug")
endif ()

if (DIMACS)
    add_definitions(-DDIMACS)
    message(STATUS "Enabled dimacs output")
endif ()

if (FORCE_NDEBUG)
    message(STATUS "Forcing NDEBUG")
    add_definitions(-DNDEBUG)
endif()

add_executable(UPCoP
        CadicalWrapper.cpp
        CLIParser.cpp
        ConnectionCalculus.cpp
        utils.cpp
        term.cpp
        propagator_base.cpp
        matrix_propagator.cpp
        adt_solver.cpp
        cnf.h
        clause.cpp
        clause.h
        fo_literal.cpp
        fo_literal.h
        ground_literal.cpp
        ground_literal.h
)

target_link_libraries(UPCoP PRIVATE ${Z3_LIB})
target_link_libraries(UPCoP PRIVATE ${CADICAL_LIB})

include(CheckIPOSupported)
check_ipo_supported(RESULT lto OUTPUT error)

if (lto AND NOT (CMAKE_BUILD_TYPE MATCHES Debug))
    message(STATUS "LTO enabled")
    set_property(TARGET UPCoP PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
