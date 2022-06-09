# Tableau for Modal Logic in LEAN

[![CI status](https://github.com/m4lvin/tablean/actions/workflows/build.yml/badge.svg)](https://github.com/m4lvin/tablean/actions/workflows/build.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/m4lvin/tablean)

We formalise a tableau system for modal logic, with the goal to prove soundness, completeness and [Craig Interpolation](https://en.wikipedia.org/wiki/Craig_interpolation).

For now we only consider the basic modal logic K, but the (very) long term goal is [Propositional Dynamic Logic](https://plato.stanford.edu/entries/logic-dynamic/) (PDL).
We try to follow the definitions and ideas from [Borzechowski (1988/2020)](https://malv.in/2020/borzechowski-pdl/).


## How To

### GitPod

[Click here to open this repository in your browser via GitPod](https://gitpod.io/#https://github.com/m4lvin/tablean).

### Local

First install Lean and tools: <https://leanprover-community.github.io/get_started.html>

Then do this:

    leanproject get m4lvin/tablean
    cd tablean
    leanproject build

## Basic Modal Logic

- [x] Soundness
- [x] Completeness
- [x] Interpolation

Module dependency overview:

![Dependency graph](./dependencies.svg)


## Inspiration / References / Related Work

- https://github.com/ljt12138/Formalization-PAL — see also https://arxiv.org/abs/2012.09388

- https://github.com/paulaneeley/modal — see also https://www.youtube.com/watch?v=kXCB5wzQTKc

- https://github.com/minchaowu/ModalTab — see also https://doi.org/10.4230/LIPIcs.ITP.2019.31

- https://github.com/bbentzen/mpl/ — see also https://arxiv.org/abs/1910.01697

- https://github.com/LudvikGalois/coq-CPL-NNF-tableau

- https://github.com/m4lvin/modal-tableau-interpolation

- https://github.com/FrancescaPerin/BScProject — see also https://fse.studenttheses.ub.rug.nl/20770/


## Acknowledgements

For their helpful advice and code hints I would like to thank
Alex J. Best,
Emma Brakkee,
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
