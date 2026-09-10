---
slug: oeis-a363184-bilateral-quarter-double-shift-theta-mod-four
bibkey: hanna2023a363184
doi: null
url: https://oeis.org/A363184
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/BilateralQuarterDoubleShiftThetaModFour
---

# The A363184 bilateral quarter-double-shift theta congruence

## Problem

OEIS A363184 (Paul D. Hanna, May 20, 2023), quoted verbatim from
`Library/Recurrence/hanna2023a363184.md`:

NAME:

> Expansion of g.f. A(x) satisfying 4 = Sum_{n=-oo..+oo} (-1)^n * x^n * (4*A(x) + x^(2*n-1))^(n+1).

COMMENT:

> Conjecture: g.f. A(x) == theta_3(x^2) (mod 4); a(n) == 2 (mod 4) if n = 2*k^2 for integer k > 0, and a(n) == 0 (mod 4) if floor(n/2) is nonsquare.

The NAME is formalised coefficientwise with exact finite windows after
cancelling the two Laurent terms. The g.f. clause is `mod_four_identity`, the
full coefficient classification is `hanna_conjecture`, and the COMMENT's
weaker zero clause is `hanna_conjecture_floor`. This dossier has one resolution
claim, attached only to `hanna_conjecture`.

## Motivation

This is a first-tier OEIS conjecture from the 2023 entry. The target proves
the classification at every positive index. KPI: open problems resolved.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches. This is a bounded literature search,
not a proof of absence or a first-publication claim.

## Route

The bilateral NAME has exponent `2n - 1`. Its formal interpretation uses the
same exact finite-window convention as the sibling A363104 module,
`D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour`, in the same
bucket. No A363104 definitions are imported or aliased.

After the Laurent monomials at zero and minus one cancel, `bilateralTerm A n`
has cases `n = 0` giving `4A`, `n = -1` giving zero, `n >= 1` giving
`(-1)^n X^n (4A + X^(2n-1))^(n+1)`, and `n <= -2` giving
`(-1)^n X^(2n^2+2n-1) invOfUnit(1 + 4A X^(1-2n), 1)^(-(n+1))`.
Here integer powers of the sign denote parity; the Lean implementation uses
natural exponents through `n = m+1` and `n = -m-2`.

`bilateralTerm_coeff_eq_zero` proves that indices outside `[-N-2,N]` do not
contribute to coefficient `N`. Integral degree contraction constructs
`generatingSeries`; `generating_equation` proves its constant coefficient is
one and its exact finite-window equation. `generating_unique` identifies
every integral solution of that equation, and `a_zero` proves `a 0 = 1`.

The implementation's own d = 2 cancellation pairs opposite constant terms
at exponent `2m^2+6m+3`. Linearisation modulo sixteen and weighted telescoping
give doubled-square support. Cancelling four over the integers yields
`cancellation_identity`: there exists integral `Q` with
`1 = A * expand 2 thetaSeries + 4Q`. Here `thetaSeries` is the frozen
`ThetaSelfCompositionModFour.thetaSeries`. Since `1 + 2S` is self-inverse
over `ZMod 4`, `mod_four_identity` gives the reduction of `A` as
`expand 2` of the reduced theta series, namely `theta_3(x^2)` modulo four.

Thus `hanna_conjecture` proves, for `n >= 1`, both
`a n % 4 = 2` iff there exists `k > 0` with `n = 2*k^2`, and
`a n % 4 = 0` iff no such `k` exists. The companion
`hanna_conjecture_floor` gives `not IsSquare (n/2) -> a n % 4 = 0`;
natural division is the COMMENT's floor. Target generality is I because it
imports the frozen `ThetaSelfCompositionModFour`, whose generality is G.

## Falsifier

A positive counterexample index whose coefficient has the wrong remainder
for doubled-square membership would falsify the classification. The
orchestrator's exact coefficient check is supporting evidence only; no
finite bound substitutes for the universally quantified proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Bilateral/BilateralQuarterDoubleShiftThetaModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `bilateralTerm_coeff_eq_zero`, `generating_equation`,
  `generating_unique`, `a_zero`, `cancellation_identity`, `mod_four_identity`,
  `hanna_conjecture_floor`.
- Axioms: std3, exactly `propext`, `Classical.choice`, and `Quot.sound`,
  as reported by the implementation seat for all eight public theorems.
- Direct frozen dependency: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour`,
  statement_id `sha256:0aec24647d5df63513f2c164c40043a38afc3ac9d0a739e594942fb5328c725b`.

Exact Lean definition and equation (the private terms are expanded below):

```lean
noncomputable def bilateralTerm (A : PowerSeries ℤ) (n : ℤ) : PowerSeries ℤ :=
  if n = 0 then 4 * A else if n = -1 then 0 else
    if 0 < n then positiveTerm A (n.toNat - 1) else negativeTerm A (-n - 2).toNat

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N (4 : PowerSeries ℤ) =
      coeff N (∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm generatingSeries n) := by
  refine ⟨?_, (equation_iff _).mpr generating_fixed⟩
  rw [generating_fixed, step_constant]
```

The helper definitions, with the module's `{R : Type*} [CommRing R]`:

```lean
private noncomputable def positiveTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 1) * X ^ (m + 1) * (4 * A + X ^ (2 * m + 1)) ^ (m + 2)

private noncomputable def reciprocal (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  invOfUnit (1 + 4 * A * X ^ (2 * m + 5)) 1

private noncomputable def negativeTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 2) * X ^ (2 * m ^ 2 + 6 * m + 3) * reciprocal A m ^ (m + 1)
```

Honesty boundary: no bilateral infinite sums of formal series in Mathlib
are asserted. The theorem concerns the explicit cancelled, coefficientwise
finite-window interpretation of the NAME, not analytic convergence or a
new Laurent-series summation operation. Source-to-formal identification is
an explicitly documented interpretation, not a kernel-checked OEIS fact.

## Triage

`theorem`. The formal proof closes the coefficient classification in the
stated interpretation, with the g.f. and nonsquare-floor companions.

## ASSUMED-UNVERIFIED

The OEIS quotes were supplied by the orchestrator. The OEIS revision history
was read by the search seat, not this seat. Literature scope was the entry,
its revision history, and identifier searches on arXiv, MathOverflow, and
GitHub as of the search date 2026-09-09; this seat had no network access.
No exhaustive literature coverage or first-publication priority is claimed.
The orchestrator's exact numerical check and external build results are
reported supporting evidence, not checks repeated by Stage B.
