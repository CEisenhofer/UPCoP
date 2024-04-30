## UPCoP

This is a prototype for encoding connection calculus matrix proofs in SAT/SMT (first-order theorem prover).

## Build

The build process was tested successfully built on Linux (gcc-11.4).

Requirements apart from a C++ 17 compiler:
- cmake
- [Z3](https://github.com/Z3Prover/z3/releases)
- [CaDiCal](https://github.com/arminbiere/cadical)

### Instructions

Get (or compile) Z3 and CaDiCal. For CaDiCal you need a version which supports ipasirup (user-propagation).
Open a console-window at some writeable location, clone the git-repository and navigate into the cloned repo

```
git clone https://github.com/CEisenhofer/UPCoP.git
cd UPCoP
```

(or just download the zip from GitHub) create a folder for the compiled output and run cmake

```
mkdir release
cd release
cmake -DCMAKE_BUILD_TYPE=Release -DCADICAL_LIB="[path-to-cadical]/libcadical.a" -DCADICAL_HEADER="[path-to-cadical]/src/" -DZ3_LIB="[path-to-z3]/libz3.so" -DZ3_HEADER="[path-to-z3]/include/" ..
cmake --build .
```

Replace "[path-to-z3]" and "[path-to-cadical]" by the path to the respective directories.
The compiled program will be likely put in the sub-directory `bin` of the directory where you invoked `cmake`

## Usage

You can run the program by calling it via command-line arguments.
```
UPCoP [arguments] path-to-input-file
```

The relevant arguments are currently:

- `-t [num]` timeout in milliseconds
- `-m [rect|core|hybrid]` defines the encoding
    - `rect` limits the number of clause copies in the proof and increases this number on failure
    - `core` uses an individual counter for each clause specifying how many copies might be used in the proof (uses unsat core to increase this number on failure)
    - `hybrid` uses a combination of both approaches
- `-d [num]` limits the depth to the respective number
- `--sat` uses CaDiCal rather than Z3 (default)
- `--smt` uses Z3 rather than CaDiCal
- `-c [auto|keep|pos|neg|min]` conjecture selection
  - `keep` uses the conjectures given in the input file - if there are none it uses `auto`
  - `pos` take all purely positive clauses
  - `neg` take all purely negative clauses
  - `min` take either `keep`, `pos` or `neg` depending on which has the smallest number of clauses

As SMTLIB does not provide a way to declare clauses as conjectures, you can declare a function `|#|` that marks clauses as conjectures.
Example: 
```
(declare-sort S 0)
(declare-fun |#| (Bool) Bool)
(declare-fun P (S) Bool)
(declare-fun Q (S) Bool)
...
(assert (|#| (forall ((x S)) (or (P x) (not (Q y))))))
```