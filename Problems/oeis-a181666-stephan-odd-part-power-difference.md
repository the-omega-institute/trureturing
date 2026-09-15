---
slug: oeis-a181666-stephan-odd-part-power-difference
bibkey: stephan2010a181666
doi: null
url: https://oeis.org/A181666
triage: theorem
motivation_gids:
  - D5/S3/Arith/StephanOddPartPowerDifference.result
---

# Stephan's A181666 odd-part power-difference characterization

## Problem

OEIS A181666, NAME (`%N`, verbatim):

> Numbers whose odd part is of the form (4^k-1)/3.

COMMENT (`%C`, verbatim):

> Also, terms of A023758 divisible by 3, divided by 3 (conjectured).

AUTHOR (`%A`, verbatim):

> _Ralf Stephan_, Nov 18 2010

OFFSET (`%O`, verbatim):

> 1,2

A023758, NAME (`%N`, verbatim):

> Numbers of the form 2^i - 2^j with i >= j.

The formal predicates avoid natural-number division. Membership in A181666 is
written as `3 * ordCompl[2] n + 1 = 4 ^ k` for some `k >= 1`, where
`ordCompl[2] n` is the odd part. The A023758 description is written as
`3 * n + 2 ^ j = 2 ^ i` with `j < i`, so the corresponding difference is
positive and natural subtraction is not truncated.

## Motivation

The elementary equivalence proves the still-conjectured A181666 comment by
identifying the two division-free descriptions. The novelty is the settlement
of a named sixteen-year-old assertion, not the technique: the proof uses the
2-adic decomposition of a natural number, periodicity of powers of two modulo
three, prime divisibility, and arithmetic normalization.

The theorem keeps the hypothesis `1 <= n` because both source sequences are
described on their positive terms and A181666 starts with `a(1) = 1`; this
hypothesis aligns the formal statement with the source domain, not with any
need of the proof. The unqualified A023758 description includes `0` by taking
`i = j`, while the formal `j < i` condition deliberately excludes that zero
term. In fact, the two formal predicates are both false at `n = 0`, so the
equivalence itself also holds there.

## Gap

At revision #56 the A181666 COMMENT still says `(conjectured)`, with no proof
link or settlement. The listed A023758 source sentence gives `i >= j`; the
formal statement uses `j < i` to remove its zero difference and then restricts
the theorem to `1 <= n` to match the positive sequence domain. Within that
domain there is no disagreement between the source assertion and the formal
equivalence.

The proof is elementary and kernel-checked. It settles the named A181666
assertion; it does not claim a new characterization of A023758 beyond the
displayed equivalence.

## Route

Write `n = 2^j q`, where `q = ordCompl[2] n` is odd. If
`3q + 1 = 4^k`, multiplying by `2^j` gives
`3n + 2^j = 2^(j+2k)`, with a strict exponent increase because `k >= 1`.

Conversely, reduce `3n + 2^j = 2^i` modulo three. Since two has order two
modulo three, `i-j` is even; write it as `2k`. Factoring the difference of
powers shows that three divides `2^(i-j)-1`. The remaining quotient is odd,
because the power of two on the right has already accounted for the exact
2-adic factor of `n`. The odd-complement identity then gives
`3 * ordCompl[2] n + 1 = 4^k`, and `i > j` forces `k >= 1`.

## Falsifier

Any positive natural `n` satisfying exactly one of the two displayed
predicates would refute `result`. A failure of `ordCompl[2] n` to equal the
odd part of `n` would instead refute the stated interpretation of the pinned
Mathlib operator. Agreement on finitely many values cannot establish the
unbounded equivalence.

## Evidence

- Lean module: `D5/S3/Arith/StephanOddPartPowerDifference.lean`.
- The result is an unbounded symbolic equivalence, not a finite computation.
- The theorem's axiom closure is `[propext, Classical.choice, Quot.sound]`.

## Triage

`theorem`; resolution `proved` for every natural `n` with `1 <= n`.

**Not claimed:** an exhaustive literature search or priority for this proof;
any result about other OEIS entries; a statement about the zero term as an
A181666 sequence member; or that finite numerical checks replace the
unbounded formal proof.

## ASSUMED-UNVERIFIED

Literature completeness beyond the OEIS entry, its linked b-file, its linked
Hinz--Stockmeyer paper, and the bounded searches recorded in preregistration
issue #8143 is unverified. No exhaustive literature or priority claim is made.
