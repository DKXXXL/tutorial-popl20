# The Iris tutorial @ POPL'20

This tutorial comes in two versions:

- The folder [exercises](exercises): skeletons of the exercises with solutions left out.
- The folder [solutions](solutions): the exercises together with their solutions.

## Dependencies

For the tutorial material you need to have the following dependencies installed:

- Coq 8.11.2
- [Iris](https://gitlab.mpi-sws.org/iris/iris) 3.3.0

*Note:* the tutorial material will not work with earlier versions of Iris, it
is important to install the exact versions as given above.

## Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (2.0.0 or newer). You first have to add the Coq
opam repository (if you have not already done so earlier):

    opam repo add coq-released https://coq.inria.fr/opam/released

Then you can do `make build-dep` to install exactly the right version of Iris.

## Compiling the exercises

Run `make` to compile the exercises.

## Overview

Introduction to Iris and the HeapLang language:

- [language.v](exercises/language.v): An introduction to Iris's HeapLang
  language, program specifications using weakest preconditions, and proofs of
  these specifications using Iris's tactics for separation logic.
- [polymorphism.v](exercises/polymorphism.v): The encoding of polymorphic
  functions and existential packages in HeapLang.

Syntactic typing:

- [types.v](exercises/types.v): The definition of syntactic types and the
  type-level substitution function.
- [typed.v](exercises/typed.v): The syntactic typing judgment.

Semantic typing:

- [sem_types.v](exercises/sem_types.v): The model of semantic types in Iris.
- [sem_typed.v](exercises/sem_typed.v): The definition of the semantic typing
  judgment in Iris.
- [sem_type_formers.v](exercises/sem_type_formers.v): The definition of the
  semantic counterparts of the type formers (like products, sums, functions,
  references, etc.).
- [sem_operators.v](exercises/sem_operators.v): The judgment for semantic
  operator typing and proofs of the corresponding semantic rules.
- [compatibility.v](exercises/compatibility.v): The semantic typing rules, i.e.,
  the *compatibility lemmas*.
- [interp.v](exercises/interp.v): The interpretation of syntactic types in terms
  of semantic types.
- [fundamental.v](exercises/fundamental.v): The *fundamental theorem*, which
  states that any syntactically typed program is semantically typed..
- [safety.v](exercises/safety.v): Proofs of semantic and syntactic type safety.
- [unsafe.v](exercises/unsafe.v): Proofs of "unsafe" programs, i.e. programs
  that are not syntactically typed, but can be proved to be semantically safe.
- [parametricity.v](exercises/parametricity.v): The use of the semantic typing
  for proving parametricity results.

Ghost theory for semantic safety of "unsafe" programs:

- [two_state_ghost.v](exercises/two_state_ghost.v): The ghost theory for a
  transition system with two states.
- [symbol_ghost.v](exercises/symbol_ghost.v): The ghost theory for the symbol
  ADT example.

Other:

- [demo.v](exercises/demo.v): A simplified version of the development to the
  simplified case, as shown during the lecture at the POPL'20 tutorial.
  
## Documentation

The files [proof_mode.md] and [heap_lang.md] in the Iris repository contain a
list of the Iris Proof Mode tactics as well as the specialized tactics for
reasoning about HeapLang programs.

[proof_mode.md]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md
[heap_lang.md]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/heap_lang.md

If you would like to know more about Iris, we recommend to take a look at:

- http://iris-project.org/tutorial-material.html
  Lecture Notes on Iris: Higher-Order Concurrent Separation Logic
  Lars Birkedal and Aleš Bizjak
  Used for an MSc course on concurrent separation logic at Aarhus University
- https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf
  Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent
  Separation Logic
  Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars
  Birkedal, Derek Dreyer.
  A detailed description of the Iris logic and its model

## Generating the exercises

If you want to contribute to the tutorial, note that the files in `exercises/`
are generated from the corresponding files in `solutions/`. Run `make exercises`
to re-generate those files. This requires `gawk` to be installed (which should
usually be available on Linux but might have to be installed separately on
macOS).

The syntax for the solution files is as follows:
```
(* BEGIN SOLUTION *)
  solution here.
(* END SOLUTION *)
```
is replaced by
```
  (* exercise *)
Admitted.
```
and the more powerful
```
(* BEGIN SOLUTION *)
  solution here.
(* END SOLUTION BEGIN TEMPLATE
  exercise template here.
END TEMPLATE *)
```
is replaced by
```
  exercise template here.
```
