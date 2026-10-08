---
slug: sun-2013-circular-primitive-permutation-refutation
bibkey: sun2013additive
doi: 10.48550/arXiv.1309.1679
url: https://arxiv.org/abs/1309.1679
triage: theorem
motivation_gids:
  - D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result
---

# Sun's Conjecture 3.8: circular permutations with primitive adjacent products

## Problem

Zhi-Wei Sun, “Some new problems in additive combinatorics”, arXiv:1309.1679,
Conjecture 3.8:

> Let F_q be a finite field with q > 7 elements, and let a_0 be any element
> of F_q. Then there is a circular permutation (a_1, …, a_{q−1}) of all the
> nonzero elements of F_q such that all the q − 1 elements a_0 + a_1a_2,
> a_0 + a_2a_3, …, a_0 + a_{q−2}a_{q−1}, a_0 + a_{q−1}a_1 are primitive
> elements of the field F_q.

The Lean definition `claim : Prop` quantifies over every finite field and
every offset. An equivalence from `Fin (q - 1)` to the nonzero subtype
expresses that every nonzero element appears exactly once. `finRotate`
advances cyclically, including the last-to-first edge. `IsPrimitiveRoot z
(q - 1)` means exact multiplicative order `q - 1`, hence precisely that
`z` generates the multiplicative group, whose order is `q - 1`.

## Motivation

The assertion seeks one circular arrangement satisfying all adjacent
primitive-element constraints simultaneously. Its universal field and
offset quantifiers permit refutation by one admissible pair.

## Gap

Sun stated the assertion in 2013 together with a numerical remark for the
offset `a₀ = −1` only. Luo and She, “A conjecture on circular permutations over
finite fields”, arXiv:2610.06289v1 (2026), restate it as their Conjecture 1.1
with the same wording, prove it for every prime power `q > 18 888 871`, and
prove the offset `a₀ = 0` for all `q > 4`; they give no table of small fields.
The OEIS entry A229232 records only the offsets `∓1`. Within these sources the
fields of order at most `18 888 871` with nonzero offset are unsettled.

## Route

Take `F = ZMod 11` and `a₀ = 2`. Every primitive element has order ten.
The residues outside `{2,6,7,8}` are zero or have fifth or second power one,
so none has order ten. A cyclic neighbour is distinct from the vertex itself.
Direct finite arithmetic with this condition then implies that each
neighbour of vertex 2 or vertex 9 must belong to `{3,8}`. Multiplication
is commutative, so this holds for both cyclic neighbours.

For any cycle of length greater than four, the two neighbours of each
vertex are distinct. If two vertices have both neighbours in a common set
of at most two elements, their neighbour pairs coincide. Matching successors
or predecessors identifies the vertices. Interchanging the pairs forces a
four-step return, impossible for a cycle of length greater than four.
The required ten-cycle therefore cannot exist.

## Falsifier

The counterexample would fail if eleven were not a prime field order greater
than seven, the offset two were inadmissible, the primitive-element exclusions
or forced-neighbour arithmetic were incorrect, the predecessor restriction
did not follow from the cyclic conditions, or the twin-neighbour obstruction
failed at length ten. The Lean proof discharges each obligation without
enumerating all permutations or adding assumptions to `result`.

## Evidence

`D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result : ¬ claim`
specializes the universal assertion to `ZMod 11` and offset two. The reusable
theorem `twin_neighbour_obstruction` applies to arbitrary vertex types and
all cycle lengths greater than four. Finite arithmetic uses kernel-checked
`decide`; the cyclic obstruction uses finite-set cardinality and exact
integer reasoning. No `native_decide`, `sorry`, or new axiom is used.
The axiom closure of `result` is `propext`, `Classical.choice`, `Quot.sound`.

## Triage

- [proved: D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result]
  The conjecture is false at field order eleven and offset two.
- [proved: D5/S3/Arith/SunCircularPrimitivePermutationRefutation.twin_neighbour_obstruction]
  Two distinct vertices of a cycle of length greater than four cannot both
  have all their cyclic neighbours in one set of at most two vertices.
- [computed] Exhaustive Hamilton-cycle checks over every offset for the
  fields of order 8, 9, 11, 13, 17 and 19 find exactly one failing pair,
  `(q, a₀) = (11, 2)`; at `q = 11, a₀ = 2` no Hamilton path even starts at 1.
- [open] Classification of all exceptional field orders and offsets is
  not supplied by this refutation. No statement about other pairs follows
  from this single counterexample.

## ASSUMED-UNVERIFIED

Forward citations of arXiv:1309.1679 were screened through web search and the
OEIS only; no citation index was exhaustively read. The journal version
(Nanjing Univ. J. Math. Biquarterly 36 (2019)) was not compared line by line
with the arXiv text. Neither condition is a hypothesis of the refutation.
