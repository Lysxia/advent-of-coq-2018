Advent of Code 2018 in Coq
==========================

Dependencies
------------

- [coq-simple-io](https://github.com/Lysxia/coq-simple-io), master

    This project serves to test coq-simple-io and see what is missing to
    make it practical to write executable programs in Coq.

- [Coq](https://coq.inria.fr/) 8.8.2

- [OCaml](https://ocaml.org)

Install the development version of coq-simple-io with opam
----------------------------------------------------------

```sh
opam pin add coq-simple-io --dev-repo

# When coq-simple-io is updated
opam reinstall coq-simple-io
```

Build
-----

To compile and run `day01_1.v` for example:

```sh
make day01_1.native
./day01_1.native < day01.example
```
