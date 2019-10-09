## ptt

An experimental implementation of normalization by evaluation (nbe) & semantic type checking for a Martin-Löf
Type Theory with nullary internal parametricity (i.e., names). This code was obtained from
[`blott`](https://github.com/jozefg/blott), an implementation of modal dependent type theory, by removing the
modal constructs and adding internal parametricity primitives. The remainder of this README has been shameless
copied from that of `blott`.

For examples, see the `test/` directory.

## building

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
run with the following:

```
$ dune exec ./src/bin/main.exe [file]   # from the `ptt` top-level directory
```
