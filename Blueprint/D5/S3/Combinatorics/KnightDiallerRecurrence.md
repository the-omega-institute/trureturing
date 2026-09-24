# The Knight-Dialler Recurrence

## Abstract

The knight-dialler counts satisfy the conjectured fourth-order recurrence, because the residual of that recurrence on the all-ones vector sits entirely on the one key a knight can never leave, and one further step annihilates it.

**Definition 1.1 (Knight adjacency on the keypad).**

$$Knight(i) = \{j \in Fin 10 \mid adjacency i j\}$$

*Formalization.* `D5/S3/Combinatorics/KnightDiallerRecurrence.adjacency` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A327692, Number of length-n phone numbers that can be dialed by a chess knight on a 0-9 keypad that starts on any number and takes n-1 steps*. URL: <https://oeis.org/A327692>.

*Commentary.*

The keypad carries the digits one to nine in three rows of three, with zero below the eight and the two cells beside it blank. Two digits are adjacent when a chess knight moves between their cells. The relation is symmetric and has no loop, and the out-degrees are two at every digit except three at four and at six, and zero at five: both knight images of the five are blank cells, so the five is a key a knight can never leave.

**Definition 1.2 (Dialable sequences).**

$$dial(n) = \lvert \{s \mid \forall i \in Fin n,\; adjacency s(i) s(i + 1)\} \rvert$$

*Formalization.* `D5/S3/Combinatorics/KnightDiallerRecurrence.dial` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A327692, Number of length-n phone numbers that can be dialed by a chess knight on a 0-9 keypad that starts on any number and takes n-1 steps*. URL: <https://oeis.org/A327692>.

*Commentary.*

A dialable sequence of n steps assigns a digit to each of the n plus one positions so that consecutive digits are knight-adjacent. The digits form a finite type, so these sequences form a finite set and can be counted, with no start digit preferred. In the source entry's indexing, the count at n steps is the term at n plus one.

**Definition 1.3 (The conjectured recurrence).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; dial(n + 5) + 4 \cdot dial(n + 1) = 6 \cdot dial(n + 3))$$

*Formalization.* `D5/S3/Combinatorics/KnightDiallerRecurrence.claim` (`✓ std3`).

*Citation.* Colin Barker (2019). *OEIS A327692, Number of length-n phone numbers that can be dialed by a chess knight on a 0-9 keypad that starts on any number and takes n-1 steps*. URL: <https://oeis.org/A327692>.

*Commentary.*

The source asserts a fourth-order recurrence with constant coefficients, in the range beyond the sixth term, and a later comment on the entry extends the range to the sixth term itself. The form recorded here is additive, because truncated subtraction on the natural numbers would silently weaken the assertion at exactly the small arguments where it is tightest.

**Theorem 1.4 (The recurrence holds).**

$$\forall n \in \mathrm{Nat},\; dial(n + 5) + 4 \cdot dial(n + 1) = 6 \cdot dial(n + 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/KnightDiallerRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/knight-dialler-recurrence` (proved) by `D5/S3/Combinatorics/KnightDiallerRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"knight-dialler-recurrence","declaration_gid":"D5/S3/Combinatorics/KnightDiallerRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker (2019). *OEIS A327692, Number of length-n phone numbers that can be dialed by a chess knight on a 0-9 keypad that starts on any number and takes n-1 steps*. URL: <https://oeis.org/A327692>.

*Commentary.*

Let the transfer vector at n steps carry, at each digit, the number of dialable sequences of n steps starting there. At zero steps it is all ones, and at each further step every entry becomes the sum of the entries at its knight neighbours. The count over all starting digits is the sum of its entries. The bridge from the cardinality to that recursion is the proved part: the sequences starting at a given digit whose second digit is a fixed neighbour correspond, by deleting the head and by prepending it, to the sequences of one step fewer starting at that neighbour, and counting fibrewise turns the cardinality into the transfer step. The step is linear, so it carries the identity from one place to the next. The base case is an evaluation: the residual of the recurrence on the all-ones vector is not zero but is supported on the five alone, and one further step annihilates it because the five has no knight neighbour. That single fact also fixes the range, the identity failing one place earlier, where the two sides differ by exactly that residual. No eigenvalue, no diagonalisability and no real spectrum enter.

## References

- Truth anchor: `D5/S3/Combinatorics/KnightDiallerRecurrence.adjacency`
- Truth anchor: `D5/S3/Combinatorics/KnightDiallerRecurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/KnightDiallerRecurrence.dial`
- Truth anchor: `D5/S3/Combinatorics/KnightDiallerRecurrence.result`
