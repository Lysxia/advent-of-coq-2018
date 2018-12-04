Advent of Code 2018 in Coq
==========================

This repository contains formally verified solutions for the Advent
of Code 2018 (https://adventofcode.com/2018). This is an example of
applying verification to small programming challenges of that kind.
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
make day01_1.native
./day01_1.native < day01.example
```
