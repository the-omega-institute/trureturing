---
slug: hardin-a235291-two-column-recurrence
bibkey: hardin2014a235291
doi: null
url: https://oeis.org/A235291
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result
---

# Hardin's signed order-four recurrence for two-column arrays

## Problem

For each positive integer $n$, let $a(n)$ count indexed $(n+1)\times2$
arrays over $\{0,1,2,3\}$ such that each contiguous $2\times2$ block has
absolute difference 3 between its diagonal and antidiagonal sums.
Hardin's formula is
$$
a(n)=14a(n-2)-48a(n-4) \qquad (n\ge5).
$$
The offset is one, so the first identity has left index five.
[OEIS source and exact locators](../Library/Automata/hardin2014a235291.md)

### Statement echo

| Published clause | Lean counterpart |
| --- | --- |
| Literal indexed arrays with $n+1$ rows, two columns and symbols 0 through 3 | `Grid 3 n 1` in `HardinA235280A235310Alphabet` is a function on pairs of indexed cells into `Fin 4`. |
| Every contiguous block has absolute diagonal difference 3 | `Legal 3` quantifies over the upper-left row and column indices and applies `Int.natAbs` to the difference of the two signed sums. |
| Count each legal filling once | `C 3 3 n 1` is the cardinality of the subtype of legal grids. Currying identifies these grids with indexed sequences of legal rows. |
| Every left index at least five and the signed lags | `result` has `n : ℕ` and `5 ≤ n`. It uses lags `n - 2` and `n - 4` with coefficients 14 and −48 in `ℤ`. |

## Motivation

The OEIS formula predicts the count at every larger height from two
earlier heights. The column of the more general rectangular table
gives the same counts. [Preregistration #34391](https://github.com/the-omega-institute/trureturing/issues/34391)

## Gap

Revision 11 labels the formula empirical. The bounded literature screen
found no exact proof or counterexample. The common order-ten rectangular
law discussed in the preregistration leaves this shorter recurrence and
its first positive windows to be established.
[Preregistered literature screen](https://github.com/the-omega-institute/trureturing/issues/34391)

## Route

A row has $4-|d|$ fillings at signed difference $d$. A next row is allowed
exactly when its difference is three away. The resulting transfer on
seven difference classes includes the multiplicity of the next row.
After one step the two ends of the component $\{-3,0,3\}$ have equal
values. On that subspace two steps multiply this component by eight and
the two remaining components by six. The polynomial
$(X^2-6)(X^2-8)$ therefore gives the recurrence. The sum over first rows,
with unit terminal weights, is the literal count.

## Falsifier

An exact legal-grid count that violates the signed identity at any
left index $n\ge5$ would refute the published assertion.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result`.
It applies to the existing literal count and uses `propext`,
`Classical.choice` and `Quot.sound`.
[Independent replay and settlement of #34391](https://github.com/the-omega-institute/trureturing/issues/34391#issuecomment-7183803813)

## Triage

### What the settlement shows

The two distinct two-step multipliers yield the signed order-four law
proved by `result`. The transfer proof works pointwise with arbitrary
integer weights on the final difference class. The count uses unit
terminal weights. An indicator weight selects a final difference class
in the transfer. The order-four law specializes the general table to
its two-column slice. Minimal order and other widths remain open
within this dossier.

## ASSUMED-UNVERIFIED

The bounded literature screen leaves global literature coverage and the
complete citation graph unverified.
