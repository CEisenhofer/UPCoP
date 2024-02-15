cmake_minimum_required(VERSION 3.16.3)

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

if (FORCE_NDEBUG)
    message(STATUS "Forcing NDEBUG")
    add_definitions(-DNDEBUG)
endif()

add_executable(UPCoP
        CadicalWrapper.cpp
        CLIParser.cpp
        ConnectionCalculus.cpp
        utils.cpp
        Term.cpp
        PropagatorBase.cpp
        matrix_propagator.cpp
        ADTSolver.cpp
        CNF.h
        Clause.cpp
        Clause.h
        Literal.cpp
        Literal.h
        GroundLiteral.cpp
        GroundLiteral.h
)

target_link_libraries(UPCoP PRIVATE ${Z3_LIBRARIES})
target_link_libraries(UPCoP PRIVATE ${CADICAL_LIBRARIES})

include(CheckIPOSupported)
check_ipo_supported(RESULT lto OUTPUT error)

if (lto AND NOT (CMAKE_BUILD_TYPE MATCHES Debug))
    message(STATUS "LTO enabled")
    set_property(TARGET UPCoP PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
