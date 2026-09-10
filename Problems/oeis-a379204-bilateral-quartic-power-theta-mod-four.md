---
slug: oeis-a379204-bilateral-quartic-power-theta-mod-four
bibkey: hanna2024a379204
doi: null
url: https://oeis.org/A379204
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour
---

# Hanna's A379204 evenness conjecture

## Problem

OEIS A379204 (Paul D. Hanna, Dec 20 2024) gives the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2024a379204.md`:

> G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 4)^(n+1).

> Conjecture: a(n) is even for n > 1.

The evenness conjecture is this dossier's sole resolution claim, anchored by
`hanna_conjecture`. The entry also states:

> Conjecture: a(n) == 2 (mod 4) iff n = (k-1)^2 + 1 for some k > 1.

The companion `hanna_conjecture_mod_four` proves that second conjecture. The
NAME is formalized after multiplication by x*A, using exact finite coefficient
windows; the source-to-formal interpretation is bounded as described below.

## Motivation

This is a first-tier OEIS conjecture from 2024. The KPI is open problems
resolved: one explicit dossier anchor for the evenness conjecture, with the
second conjecture proved as a companion result.

## Gap

The supplied search record reports no proof found: the search seat read the
OEIS entry and revision history on 2026-09-09 and searched the identifier on
arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access and
did not independently repeat those searches. Absence from those searches is
not a proof of publication priority.

## Route

The bilateral NAME is read after multiplication by x*A. For integer n,
`bilateralTerm A n` is its ordinary power-series term, except at n = -1,
where it is zero: the Laurent summand is A^(-1), whose leading Laurent part
is x^(-1) under the normalization, and multiplication by X*A contributes
the isolated X. For n = -r with r >= 2, factoring the negative powers gives
the nonnegative power of A and the unit inverse used in `bilateralTerm`.
`bilateralTerm_coeff_eq_zero` bounds the exact finite window: all omitted
terms have zero coefficient at degree N. `generating_equation` states
A(0) = 0, a(1) = 1 and the coefficient identity with indices in
`Finset.Icc (-(N : ℤ) - 2) N`.

The honesty boundary, also used by the landed `BilateralThetaReversionModSixteen`,
is that Mathlib has no bilateral infinite sums of formal series. The theorem
therefore uses exact finite windows, not a separately defined bilateral
infinite-sum object or analytic convergence claim. `generating_unique` proves
uniqueness by degree contraction for this zero-constant coefficient equation.

Pairing indices m and -m-2 in each window gives doubled square powers after
multiplication by A and reduction modulo four. Reduction modulo two yields
`mod_two_identity`, A-bar = X over ZMod 2. A mod-two-to-mod-four doubling lift
replaces the doubled powers of A by those of X. The reduced factor is
1 + 2*Sum_{j>=1} X^(j^2), the frozen
`ThetaSelfCompositionModFour.thetaSeries`; `mod_four_identity` gives
A-bar = X*theta-bar_3 over ZMod 4.

Thus `hanna_conjecture_mod_four` proves, for n >= 1, both
`a n % 4 = 2 ↔ ∃ k : ℕ, 1 < k ∧ n = (k - 1)^2 + 1` and
`a n % 4 = 0 ↔ 1 < n ∧ ¬ ∃ k : ℕ, 1 < k ∧ n = (k - 1)^2 + 1`.
The `1 < n` guard in the latter is necessary because a(1) = 1. The two
remainders imply `hanna_conjecture`: n > 1 implies `Even (a n)`, the sole
claim. Target generality is I because the proof imports frozen
`D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour` (itself G).

## Falsifier

An index n > 1 with odd a(n), for the unique normalized finite-window
solution, would contradict the claim. The orchestrator's exact coefficient
check is supporting evidence only; it does not replace the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.lean`.
- Main theorem and sole explicit resolution anchor: `hanna_conjecture`.
- Companions: `bilateralTerm_coeff_eq_zero`, `generating_equation`,
  `generating_unique`, `mod_two_identity`, `mod_four_identity`,
  `hanna_conjecture_mod_four`.
- Axioms: std3, exactly `[propext, Classical.choice, Quot.sound]`, as reported
  by the implementation seat for all seven public theorems.

The exact Lean interpretation of the NAME is:

```lean
theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧ ∀ N, coeff N generatingSeries =
      coeff N (X + X * generatingSeries *
        ∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm generatingSeries n)
```

This is the finite-window formal-series assertion after multiplying by X*A;
it does not assert the existence of a Mathlib bilateral infinite-sum object.

## Triage

`theorem`. The formal proof closes the evenness assertion for every n > 1
under the stated formal reading of the NAME.

## ASSUMED-UNVERIFIED

The OEIS quotes and attribution were supplied by the orchestrator. The OEIS
revision history was read by the search seat, not by this seat. Literature
coverage was the OEIS entry/history and identifier searches on arXiv,
MathOverflow, and GitHub; this seat had no network. The absence of an
independent proof, first-publication priority, and identification of the OEIS
Laurent equation with the finite-window formalization are not kernel-checked
facts. The orchestrator's exact coefficient check and external build gates
were supplied evidence, not checks executed by this seat.
