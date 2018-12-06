(These notes need to be cleaned up into some write up somewhere.)

---

For programs with so little interactivity, read/write might be too
granular. So far all exercises fit the read_all pattern. To make
things a bit more interesting and also more performant, I also try
to use a finer fold_read pattern where possible.

Day 5, part one, is a bit special about input handling: with
byte-by-byte input you need to be careful about the newline character.
Problems with less regular input might find read/write more useful.

---

What even is a spec?

- In day 1, part one, some might actually find the imperative style
  of [main] easier to understand than the recursive [sum_Z].

- In day 1, part two, the current spec basically says "if there is a
  duplicate, then [main] prints the first one".

  + we haven't proved that the existence of a duplicate
    implies [first_dup];

  + How do we know the precondition is satified by our input?
    If it is not, then the spec tells us nothing. A better spec is:
    if [main] prints anything, it is the first duplicate.

- In day 5, a naive approach is to only prove
  [fully_react input (react input)]. However I think the uniqueness
  of the solution is an important part of the problem, which motivates
  the proof of confluence.
