---
slug: oeis-a363560-cubic-ninth-power-substitution-mod-three
bibkey: hanna2023a363560
doi: null
url: https://oeis.org/A363560
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree
---

# Divisibility of the A363560 coefficients

## Problem

OEIS A363560, Paul D. Hanna, Aug 12 2023, records the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2023a363560.md`:

> Expansion of g.f. A(x) satisfying A(x)^3 = 1 + x*(A(x) + A(x)^2 + A(x)^9).

> Conjecture: a(n) == 0 (mod 3) for n > 0 except when n == 1 (mod 7).

## Motivation

This is the first-tier recent OEIS conjecture selected in the implementation
brief. The KPI is open problems resolved. The target is the universal
divisibility assertion for the normalized integral generating series.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches. This bounded search is not a claim of
exhaustive literature coverage or first-publication priority.

## Route

The exact polynomial factorization is
`t + t² + t⁹ = (t² + t + 1)·P(t)`, where
`P(t) = t − t³ + t⁴ − t⁶ + t⁷`. For B in ℤ⟦X⟧ with constant coefficient 1,
the factor `B² + B + 1` has constant coefficient 3 and is nonzero.
Non-zero-divisor cancellation gives `cubic_iff_fixed`:
`B³ = 1 + X·(B + B² + B⁹) ⟺ B = 1 + X·P(B)`.

A is the stabilised integral fixed point of `Φ(F) = 1 + X·P(F)` (multiplier 1).
Multiplication by X improves coefficient agreement by one degree.
`generating_equation` proves both `A(0) = 1` and the original cubic equation
`A³ = 1 + X·(A + A² + A⁹)`. `generating_unique` passes any normalized integral
solution through the equivalence and the contraction to identify it with A.

Over ZMod 3, put `B = Ā − 1`. Characteristic-three polynomial reduction gives
`P(1 + B) = 1 + B⁷`, hence `B = X·(1 + B⁷)`. Bounded convolution with strong
induction proves that B is supported only on indices congruent to 1 modulo 7.
Thus `hanna_conjecture` proves `3 ∣ a(n)` for every `n > 0` with `n % 7 ≠ 1`.
Non-vanishing on the class congruent to 1 is not claimed. The module has
Mathlib-only imports, no D5 import, and generality G.

## Falsifier

A positive index n with `n % 7 ≠ 1` whose coefficient in the normalized
integral solution is not divisible by 3 would contradict the assertion.
The orchestrator's exact coefficient check is supporting evidence only;
the proof has no finite search bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.lean`.
- Main theorem: `hanna_conjecture`.
- Companion theorems: `cubic_iff_fixed`, `generating_equation`, `generating_unique`.
- Axioms: std3, exactly `propext`, `Classical.choice`, `Quot.sound` for each
  public theorem, as recorded by the implementation seat.

## Triage

`theorem`. The formal proof closes the universal divisibility assertion
recorded by OEIS for the normalized integral generating series.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from the Library
note. The OEIS revision history was read by the search seat, not this seat.
The reported literature scope was the OEIS entry and revision history plus
identifier searches on arXiv, MathOverflow, and GitHub on 2026-09-09; this seat
had no network access. Completeness of the literature search, publication
priority, and source-to-Lean identification are not kernel-checked facts.
