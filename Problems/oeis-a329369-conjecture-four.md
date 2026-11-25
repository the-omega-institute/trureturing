---
slug: oeis-a329369-conjecture-four
bibkey: kurkov2023a329369
doi: null
url: https://github.com/oeis/oeisdata/blob/e04da2424e051c6a20f500f80ae1c3d04e4b181f/seq/A329/A329369.seq#L32
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4
---

# Kurkov's signed factorial-power identity

## Problem

Mikhail Kurkov’s January 23, 2023 FORMULA block in A329369 revision 239
prints the conjecture below. [Conjecture 4, FORMULA line 32](https://github.com/oeis/oeisdata/blob/e04da2424e051c6a20f500f80ae1c3d04e4b181f/seq/A329/A329369.seq#L32)

> Conjecture 4: a(2^m*(2k+1)) = Sum_{i=1..wt(k) + 2} i!*i^m*A358612(k, i)*(-1)^(wt(k) - i) for m >= 0, k >= 0 where wt(n) = A000120(n).

A329369 counts permutations of `{1,…,M}` whose strict excedance set consists
of the positions `M−i` for `0<i<M` with bit `i−1` of the index set to one.
An admissible size satisfies `M≥1` and `n<2^(M−1)` for the index `n`.
The order-preserving bijection `j ↦ j+1` transports permutations and strict
excedances. With `w=M−1` and `j+1=M−i`, the source bit `i−1` is
`w−1−j`. The last position cannot be a strict excedance.

The second printing reverses the equality and uses the exponent
`wt(k)−i+2`. [A358612 revision 52](https://raw.githubusercontent.com/oeis/oeisdata/d8ad22d9b98d2c427be8c6cd9f2672c600b8e3ae/seq/A358/A358612.seq)

The source notes give the immutable revisions, transcripts and scalar
recursion. [A329369 Conjecture 4 note](../Library/PermutationPatterns/kurkov2023a329369.md) · [A358612 note](../Library/Digit/kurkov2024a358612.md)

| Source clause | Lean counterpart |
| --- | --- |
| All natural `m,k` and admissible sizes `M` | `conjecture4 (m k w : ℕ)` with `w=M−1` and the width guard |
| Exact strict excedances | `binaryExcedances` uses bit `w−1−j` at zero-based position `j<w` |
| Cardinality of the actual permutations | `paddedCount` uses `Nat.card` of the prescribed subtype |
| Binary weight and literal rational array | `DyadicRowPolynomialRecurrence.wt` and `DyadicExtendedStirlingBlock.T` |
| Factorial, power, full summation interval and sign | Rational `i!` and `i^m` on `Finset.Icc 1 (wt k + 2)` with integer exponent `wt(k)−i` |

## Motivation

The identity connects permutation counts with all coefficients of the
extended Stirling rows. Its two parameters range independently over the
natural numbers. The prospective delivery record states the complete
unbounded Tier 1 identity and the repair acceptance criteria.
[#32178](https://github.com/the-omega-institute/trureturing/issues/32178)

## Gap

The bounded literature screen in the original registration identified the published
word recurrences of Ehrenborg and Steingrímsson, Alekseyev's two-block
formulas as printed in A329369, and related MathOverflow results. Within
the inspected material it found no proof of the full transform for the
literal scalar array and the exact count. MathOverflow answer 474668 itself,
the current body and status of question 486535, exhaustive citation coverage,
MathDB and access-limited OpenAlex results remain unverified. The archived
status of question 483753 is limited to that capture. Priority is open.
[#31021](https://github.com/the-omega-institute/trureturing/issues/31021)

## Route

The strict-excedance deletion and adjacent-swap bijections give the odd
and positive-even count recurrences. Strong induction identifies the count
with the value at one of the row polynomial for every admissible width.
Following the literal scalar recurrence identifies the signed ascending
Pochhammer coordinates. Each doubling multiplies the coordinate of order
`i` by `i`, and evaluation at one gives `i!`. The two signs agree since
their exponents differ by two throughout the summation interval.

## Falsifier

An admissible `m,k,M` with a different one-based permutation count refutes
the identity. A discrepancy in the scalar recursion, cardinality map,
index bounds, casts or sign would invalidate the source correspondence.

## Evidence

The compiled, canonically frozen theorem is
`D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4`.
It covers every admissible size and both zero parameters. Local verification
covers the affected Lean modules and their imports, the Reg mirrors, and
the one-based statement applied to the frozen theorem. The theorem uses
`Classical.choice`, `Quot.sound`, and `propext`.
[Theorem and source correspondence](../Blueprint/D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.md)

## Triage

- The derivation yields the factorial-power moment formula for the counts
  along each fixed odd index followed by any number of doublings.
- The formula and the row-edge identity address distinct questions about
  the same rational array.
- The exact identity is proved.

## ASSUMED-UNVERIFIED

The bounded literature screen has the access limits recorded above.
It does not establish priority or exhaustive coverage.
