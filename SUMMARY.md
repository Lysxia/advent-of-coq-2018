# The Advent of Code in Coq: Project summary

Programming challenges like the Advent of Code usually focus more
on algorithmic content, keeping IO to the bare minimum. Thus, a
traditional approach would be to similarly concentrate on verifying
pure functions at the core of the given problem. In contrast, this
project aims to cover IO handling, to get closer to the ideal of a
"complete certification". In spite of the simple format of the Advent
of Code, formally specifying the IO interface in a satisfactory way
took quite some trial and error, even with significant simplifications.

## Challenges

### How to do IO in Coq?

At its core, Coq is only a very expressive lambda calculus, with
no notion of IO to speak of. One standard way to "run" Coq terms
is to extract them to OCaml (also SML and Haskell). This is well
adapted to implement pure algorithms in Coq and link them in OCaml,
but we can also use extraction to declare abstract primitives that
extract to whatever OCaml code we want. That way, Coq has a somewhat
practical FFI story.

Using that mechanism, I created
[coq-simple-io](https://github.com/Lysxia/coq-simple-io) to define
an IO monad mimicking Haskell.

### How to verify IO programs?

As the documentation of coq-simple-io indicates, verification-wise,
it comes with no batteries. The idea is to keep it light so it can
be plugged into various verification frameworks without regret,
since, AFAICT, there is no One True Way of verifying IO programs.

But still, without verification, this project would not be too
different from doing it in OCaml directly. So let's try verifying
our solutions! An expected side product of this project is a
little verification framework suitable for programming challenges
like the Advent of Code.

As with any verification project, there is no way to get 100%
confidence: there will always be some unchecked component to be
trusted, and experience shows it is subject to [the 80/20
principle](https://en.wikipedia.org/wiki/Pareto_principle).
Thus we have to pick our battles. For this project, the battle
stops at parsing. The Advent of Code solutions use and trust a
simple API with structured inputs/outputs, e.g., with `Z`:

```coq
(* [lib/io.v] *)
Parameter read : IO Z.
Parameter print : Z -> IO unit.
```

In fact, the API is parameterized by the types of inputs and outputs,
which may thus change for each problem. For example, Day 1 deals with
signed integers, and Day 2 deals with strings.

The current implementations of `read` actually process the input
line by line, so in a way, we are still handling a small aspect of
parsing.

For verification, we model the `IO` monad as a "State monad"
`IO A = io_state -> io_state * A` for some type `io_state`
representing a simple world:

```coq
(* [lib/rel.v] *)
Record io_state I O := Mk_io_state {
  input : list I;
  output : list O;
}.
```

There is one little issue: the API comprises a general fixpoint
combinator:

```coq
(* coq-ext-lib library *)
Class MonadFix (m : Type -> Type) : Type := {
  mfix : forall A B, ((A -> m B) -> (A -> m B)) -> A -> m B;
}.
```

This `mfix` cannot be implemented for a pure state monad in Coq.
After many failed attempts (some of which are recorded in
`lib/mock.v` and `lib/mock_spec.v` for posterity, but also because
I hope to figure them out one day), I've currently settled for
defining partial functions as relations (big-step style):

```coq
(* [lib/rel.v] *) (* This is a monad. *)
Definition io_rel I O A :=
  io_state I O -> io_state I O -> A -> Prop.
```

The definition of `mfix` is still non-trivial IMO, but users don't
have to see it, they only need to know that it defines a fixed point,
with the obvious law: `mfix f = f (mfix f)`.

Now, our solutions are monadic programs, of which the monad is a
parameter. Using regular `IO`, we get executables via extraction.
Using  the `io_rel` monad shown just above, we get an abstract model
of the program as a partial function (morally
`io_state -> io_state * A`).

A toplevel `main` program only has a `unit` return type: any output
should be printed, not returned. We thus obtain a relation between
inputs and outputs:

```coq
(* [lib/rel.v] *)
Definition rel_spec I O :
  io_rel I O unit -> list I -> list O -> Prop.
```

A specification is a property of that model:

```coq
Definition specification I O : (list I -> list O -> Prop) -> Prop.
(* That definition does not actually appear in the code. *)
```

*(Advent of Code Spoilers ahead.)*

To take the example of day 1 (part one), we show that the `main`
program implements the function that sums a list of integers:
as a relation, it must relate a list `zs` to a singleton list of
`sum_Z zs`.

```coq
(* [day01_1.v] *)
Theorem correct_main :
  forall zs, rel_spec Z Z main zs [sum_Z zs].
```

Regarding the question of termination, this is a total correctness
theorem: any output in the codomain of the relation `main` means
that, on the corresponding input, the program *will* terminate and
produce that output.

I hope that gave you a taste of the kind of properties we can verify
in this project.

## Formalization gap

Verification efforts should make explicit the components they trust,
to avoid a false sense of security that comes with the currently
uncommon usage of formal verification, and more importantly to
clarify the scope of the verification results, which might also
reveal weaknesses worth reinforcing.

If you spot anything missing from this section, please open an issue!

The link between `IO` and `io_rel` (i.e., that `io_rel` properly
models `IO`, at least in this simple setting) is part of the trusted
base. In any case, since `IO` is defined via extraction, it would not
be possible to verify that link without significant effort (there's
at least a full thesis to write on that topic). A relevant project
to mention here is
[CertiCoq](https://www.cs.princeton.edu/~appel/certicoq/),
a verified compiler for Coq.

A more feasible task would be to verify the multiple variants of
`read`/`print` functions currently in use, against a smaller number
of trusted primitives and a uniform model of `IO` (that avoids the
`I` and `O` parameters of `io_rel`). My guess is this would
significantly complicate the current model, for quickly diminishing
returns, but I can be convinced otherwise.

## Repo organization

- In every `day*_*.v` file: the `main` program to be executed,
  a `correct`-ness theorem, and a proof `correct_main`.

- `lib.v`: reexports code under `lib/`, general-purpose definitions
  reusable by different solutions.

    + `lib/io.v`: IO interface used by the solutions.
    + `lib/rel.v`: modelling IO as a relation (or partial function)
      between inputs and outputs.
    + `lib/string.v`, `lib/stream.v`, `lib/utils.v`:
      various utilities complementing the stdlib.
    + `lib/mock.v`, `lib/mock_spec.v`: more functional/computational
      models of IO (WIP/failed experiment).
