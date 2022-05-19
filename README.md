# Tableau for Modal Logic in LEAN

[![CI status](https://github.com/m4lvin/tablean/actions/workflows/build.yml/badge.svg)](https://github.com/m4lvin/tablean/actions/workflows/build.yml)

We formalise a tableau system for modal logic, with the goal to prove soundness, completeness and [Craig Interpolation](https://en.wikipedia.org/wiki/Craig_interpolation).

For now we only consider the basic modal logic K, but the (very) long term goal is Propositional Dynamic Logic (PDL).
We try to follow the definitions and ideas from Borzechowski (1988/2020) <https://malv.in/2020/borzechowski-pdl/>.


## Quick How To

First install Lean and tools: <https://leanprover-community.github.io/get_started.html>

Then clone this repository and run `make` which will do `leanproject build`.

Hint: This will be faster if you first do `leanproject get-mathlib-cache`.


## Basic Modal Logic

- [x] Soundness
- [x] Completeness
- [x] Interpolation

Module dependency overview:

![Dependency graph](./dependencies.svg)


## Inspiration / References / Related Work

- https://github.com/ljt12138/Formalization-PAL

- https://github.com/paulaneeley/modal

- https://github.com/minchaowu/ModalTab — see https://doi.org/10.4230/LIPIcs.ITP.2019.31

- https://github.com/bbentzen/mpl/ — see https://arxiv.org/abs/1910.01697

- https://github.com/LudvikGalois/coq-CPL-NNF-tableau

- https://github.com/m4lvin/modal-tableau-interpolation

- https://github.com/FrancescaPerin/BScProject


## Acknowledgements

For their helpful advice and code hints I would like to thank
Alex J. Best,
Jasmin Blanchette,
Riccardo Brasca,
Kevin Buzzard,
Mario Carneiro,
Yaël Dillies,
Patrick Johnson,
Kyle Miller,
Eric Rodriguez,
Ruben Van de Velde,
Eric Wieser,
and all other friendly people at [leanprover.zulipchat.com](https://leanprover.zulipchat.com/).
