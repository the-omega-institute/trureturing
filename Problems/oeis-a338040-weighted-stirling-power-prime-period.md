---
slug: oeis-a338040-weighted-stirling-power-prime-period
bibkey: bala2022a338040
doi: null
url: https://oeis.org/A338040
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod
---

# Prime periods of the A338040 weighted Stirling power sum

## Problem

OEIS A338040, entry by Vaclav Kotesovec, Oct 08 2020, has the following
NAME, quoted verbatim from `Library/Recurrence/bala2022a338040.md`:

> E.g.f.: Sum_{j>=0} 4^j * (exp(j*x) - 1)^j.

The supplied attribution also identifies Paul D. Hanna, May 31 2022.
The COMMENT by Peter Bala, May 31 2022, states:

> Conjecture: Let p be prime. The sequence obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1.

The theorem proves periodicity with period p - 1 for every prime p and n >= 1.
It does not assert minimality of the period. The e.g.f. identity is read through
the entry's finite FORMULA quoted in Evidence; that identity is not separately
formalized.

## Motivation

This is a first-tier OEIS conjecture: the entry dates to 2020 and Bala's
conjecture to 2022. KPI = open problems resolved. The target is the universal
prime-period assertion, not a finite range of numerical checks.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. Absence of a proof in that search scope does not establish
publication priority.

## Route

`a n` is the natural-valued finite sum
`Σ_{k ≤ n} 4^k · k^n · k! · Nat.stirlingSecond n k`, the entry's finite
FORMULA and the formal reading of its e.g.f. `Σ 4^j (e^{jx} - 1)^j`.
`a_eq_window` reduces a(n) modulo p to k < p: Stirling numbers vanish above
the diagonal, and p divides k! for k >= p. The imported
`StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion` distributes
through `4^k · k^n` to give weighted powers `(k*j)^n`. Fermat applies to
nonzero bases; zero bases are handled separately using n >= 1. This proves
`bala_conjecture`, `(a (n + (p - 1)) : ZMod p) = a n`.
Induction on the nonnegative multiplier gives `bala_conjecture_periodic`.
Minimality of the period is not asserted. Target generality is I because
the proof imports the frozen `StirlingPowerFactorialPrimePeriod`, itself G
with Mathlib-only imports.

## Falsifier

A prime p and index n >= 1 such that a(n + (p - 1)) is not congruent to a(n)
modulo p would contradict the assertion. The orchestrator's exact numerical
check is supporting evidence only; the Lean theorem has no finite bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.lean`.
- Main theorem: `bala_conjecture`; companions: `a_eq_window`,
  `bala_conjecture_periodic`; public definition: `a`.
- Axioms reported by the implementation seat for all three public theorems:
  std3, exactly `[propext, Classical.choice, Quot.sound]`.
- Finite FORMULA at https://oeis.org/A338040, supplied transcription of the
  `%F` line (raw source bytes were not independently checked by this seat):

  ```text
  %F A338040 a(n) = Sum_{k=0..n} 4^k * k^n * k! * Stirling2(n,k)
  ```

  The formula text is copied from `Library/Recurrence/bala2022a338040.md`.
  The NAME's e.g.f. identity is read through this finite formula.
- Frozen dependency: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`,
  statement_id `sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.

## Triage

`theorem`. The formal proof closes the universal prime-period assertion under
the finite-FORMULA identification of the sequence.

## ASSUMED-UNVERIFIED

The OEIS quotations and attributions were supplied by the orchestrator; the
NAME, COMMENT, and finite formula were copied from its Library note. The raw
`%F` line, including any source punctuation or attribution, was not available
for independent byte-for-byte verification. The OEIS revision history was
read by the search seat, not this seat. Literature coverage was the OEIS
entry and history plus identifier searches on arXiv, MathOverflow, and GitHub
on 2026-09-09. This seat has no network. Publication priority, completeness
of that search, and the e.g.f.-to-finite-formula identification are not
kernel-checked facts.
