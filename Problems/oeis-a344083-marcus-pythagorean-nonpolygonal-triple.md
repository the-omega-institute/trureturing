---
slug: oeis-a344083-marcus-pythagorean-nonpolygonal-triple
bibkey: marcus2021a344083
doi: null
url: https://oeis.org/A344083
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.result
---

# Marcus's A344083 nonpolygonal Pythagorean triple conjecture

## Problem

Michel Marcus's COMMENT in OEIS A344083 states:

> Conjecture: there are no other Pythagorean triples that give this minimum. In other words, it is the only triple with 3 A090467 terms.

OEIS A090467 consists of the natural numbers that are not polygonal numbers
of order greater than two. In the formal statement, `nonpolygonal n` means
that no `k > 2` and `m > 2` satisfy
`n = m + (k - 2) * Nat.choose m 2`.

The conjecture asserts both that `(3,4,5)` has three nonpolygonal sides and
that every positive Pythagorean triple with three nonpolygonal sides has
unordered legs `{3,4}` and hypotenuse `5`.

## Motivation

The result resolves the full unbounded uniqueness claim, including the
existence of the named example, rather than checking a finite range of
Pythagorean triples.

## Gap

Issue #8470 records the verbatim OEIS statement, its full quantifiers, and the
checked literature surfaces. The A344083 and A090467 entries contain no proof,
refutation, or settlement marker for the conjecture. Searches of the pinned
Mathlib tree and the repository found no theorem combining Pythagorean triples
with A090467 membership.

The completed searches are bounded and do not establish exhaustive literature
coverage or publication priority.

## Route

Squares modulo three are zero or one, so the Pythagorean equation forces at
least one leg to be divisible by three. If a positive multiple `3*t` is
nonpolygonal, then `t` cannot exceed one: for `t >= 2`, the identity
`polygonal (t+1) 3 = 3*t` supplies a forbidden polygonal representation.
Thus one leg is three.

Substituting that leg into the Pythagorean equation bounds the other leg by
four and the hypotenuse by five. Exact finite cases then give the other leg as
four and the hypotenuse as five. Separately, every polygonal value with order
and index above two is at least six, so three, four, and five are all
nonpolygonal and satisfy the Pythagorean equation.

## Falsifier

A positive Pythagorean triple with three nonpolygonal sides other than
`(3,4,5)`, up to swapping its legs, would contradict the uniqueness theorem.
A polygonal representation of any of three, four, or five with both parameters
above two would contradict its existence conjunct.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.lean`.
- Resolution theorem: `result : claim`; the `Proved` resolution claim is
  attached only to this theorem.
- The private escape witness proves that every positive nonpolygonal multiple
  of three equals three and is used in both leg-order branches.
- The theorem's axiom closure is `propext`, `Classical.choice`, and
  `Quot.sound`.

## Triage

`theorem`. The Lean result proves existence and uniqueness for all positive
natural-number Pythagorean triples under the literal A090467 predicate.

## ASSUMED-UNVERIFIED

The correspondence between the OEIS prose and the formal natural-number
predicate is a source-faithfulness judgment rather than a kernel theorem. The
bounded literature search does not establish exhaustive coverage or
publication priority.
