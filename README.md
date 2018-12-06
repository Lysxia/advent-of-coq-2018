Advent of Code 2018 in Coq
==========================

This repository contains solutions for the Advent of Code 2018
(https://adventofcode.com/2018). Some of them are formally verified.
This is an example of applying verification to small programming
challenges of that kind.
(If you're aiming for prizes, this is probably not the way to go.)

Project status
--------------

As of December 2, the two solutions of Day 1's challenge are
verified (significant caveats apply).

Read more about my approach in [`SUMMARY.md`](./SUMMARY.md).

Dependencies
------------

- [coq-simple-io](https://github.com/Lysxia/coq-simple-io), master

    This project serves to test coq-simple-io and see what is missing to
    make it practical to write executable programs in Coq.

- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib), 0.10

- [Coq](https://coq.inria.fr/), 8.8.2

- [OCaml](https://ocaml.org), 4.07.0

Older versions of these are likely to work.

### Optional dependency

- [coq-itree](https://github.com/DeepSpec/InteractionTrees), master
  A library of free monads and algebraic effects (WIP).

Experimental proofs using `itree` instead of `io_rel` can be found in
files `sol/day*_*_extra.v`.

To install coq-itree with opam and make it known to advent-of-coq:

```sh
git clone https://github.com/DeepSpec/InteractionTrees
opam pin add coq-itree ./InteractionTrees

# Inside advent-of-coq-2018, create a symbolic link _CoqConfig.append to _CoqConfig.extras
# The -f option overwrites any existing _CoqConfig.append
ln -sf _CoqConfig.extras _CoqConfig.append
```

Install the development version of coq-simple-io with opam
----------------------------------------------------------

```sh
# Get the source
git clone https://github.com/Lysxia/coq-simple-io

# Register the local version of coq-simple-io with opam
opam pin add -k git coq-simple-io ./coq-simple-io

# When coq-simple-io is updated
cd coq-simple-io && git pull coq-simple-io
opam reinstall coq-simple-io
```

Build
-----

To compile and run `day01_1.v` for example:

```sh
make exe/day01_1
./exe/day01_1 < txt/day01
```
