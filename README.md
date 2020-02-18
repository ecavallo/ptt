# ptt

An experimental implementation of normalization by evaluation (nbe) & semantic type checking for a Martin-Löf
Type Theory with *n*-ary internal parametricity. This repository uses
[`blott`](https://github.com/jozefg/blott), an implementation of modal dependent type theory, as a base; the modal constructs have been removed and replaced with internal parametricity primitives.

The type theory implemented here is roughly that of [Cavallo and Harper](https://doi.org/10.4230/LIPIcs.CSL.2020.13), but is based on intensional Martin-Löf type theory rather than cubical type theory. It is thus in turn similar to that of [Bernardy, Coquand, and Moulin](https://research.chalmers.se/publication/230735). One change relative to these theories, motivated by implementation concerns, is the formulation of Gel/Ψ-types as positive (with an elimination principle) rather than negative (with a projection and eta-principle).

To enable experimentation, we include *n*-ary parametricity primitives for every (concrete) *n*. We observe, however, that iterated binary parametricity suffices to encode *n*-ary parametricity for all *n*. There is no direct interaction between parametricity primitives of different arity.

For examples, see the `test/` directory.

## Syntax

Syntax | Description
--- | ---
`[x] A {a0; ...; an}` | Type of bridges across `A` in dimension `x` with endpoints `a1`,...,`an`
`bri x -> a` | Bridge abstraction
`p @ x` | Bridge application
`Gel x {A1; ...; An} (a1 ... an -> R)` | Gel-type for an *n*-ary relation `R(a1,...,an)` on types `A1`,...,`An`
`gel x {a1; ...; an} b` | Constructor for elements of Gel-type
`ungel x : n -> p at q -> C with`<br>`\| gel b -> t` | Elimination from bridges `x.p` over an *n*-ary Gel-type into a type family `q.C`
`extent x of t in y -> A at y a -> B with`<br>`\| a0 -> b0`<br>`\| ...`<br>`\| an -> bn`<br>`\| a1 ... an q y -> b` | *n*-ary extent term mapping from `A` to `B`, casing on `x` in `t : A<x/y>`, with endpoint cases `b0`,...`bn` and bridge case `b`

Bridge-types with partially-specified endpoints can be defined using the wildcard `*`; for example, `[x] A {a0; *}` is the type of binary bridges whose `0` endpoint is `a0`. The type `[x] A {a0; a1}` is a sub-type of `[x] A {a0; *}`. 

## Building

ptt has been built with OCaml 4.06.1 and 4.07.1 with [opam 2.0](https://opam.ocaml.org/). Once
these dependencies are installed ptt can be built with the following set of commands.

```
$ opam update
$ opam pin add -y ptt .                 # first time
$ opam upgrade                          # after packages change
```

After this, the executable `ptt` should be available. The makefile can be used to rebuild the
package for small tests. Locally, ptt is built with [dune](https://dune.build), running the above
commands will also install dune. Once dune is available the executable can be locally changed and
run on a file `[file]` with the following:

```
$ dune exec ./src/bin/main.exe [file]   # from the `ptt` top-level directory
```
