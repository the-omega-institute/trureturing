---
slug: oeis-a363104-bilateral-quarter-shift-theta-mod-four
bibkey: hanna2023a363104
doi: null
url: https://oeis.org/A363104
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour
---

# The A363104 bilateral generating function modulo four

## Problem

OEIS A363104 (Paul D. Hanna, May 21 2023) gives the following NAME and
COMMENT, quoted verbatim from `Library/Recurrence/hanna2023a363104.md`:

> Expansion of g.f. A(x) satisfying 4 = Sum_{n=-oo..+oo} (-x)^n * (4*A(x) + x^(n-1))^(n+1).

> Conjecture: g.f. A(x) == theta_3(x) (mod 4); a(n) == 2 (mod 4) iff n is a nonzero square and a(n) == 0 (mod 4) iff n is nonsquare.

The NAME is formalised coefficientwise with exact finite windows after the
two Laurent terms cancel. `mod_four_identity` proves the generating-function
clause; `hanna_conjecture` proves both coefficient biconditionals. This dossier
has one resolution claim, attached only to `hanna_conjecture`.

## Motivation

This is a first-tier OEIS conjecture from the 2023 entry. The KPI is open
problems resolved; the target is the universal conjecture, not a finite prefix.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches. The literature conclusion is limited to
that reported scope.

## Route

Read the bilateral NAME formally using `bilateralTerm A n` for integer `n`.
At `n = 0` it is `4*A`; at `n = -1` it is zero, because the Laurent parts
`X⁻¹` and `-X⁻¹` at these two indices cancel. At `n >= 1` it is
`(-X)^n * (4*A + X^(n-1))^(n+1)`. At `n <= -2` it is
`(-1)^n * X^(n²+n-1) * invOfUnit(1 + 4*A*X^(1-n))^(-(n+1))`,
with the inverse taken at the unit constant coefficient one and all remaining
exponents nonnegative. The Lean definitions below reindex these cases by
natural `m`.

`bilateralTerm_coeff_eq_zero` proves every coefficient outside
`Finset.Icc (-(N : ℤ) - 2) N` vanishes. `generating_equation` gives constant
coefficient one and equality of the coefficient of four with the coefficient
of that exact finite sum at every degree `N`. As in the landed
`BilateralThetaReversionModSixteen`, the honesty boundary is explicit: this is
not a Mathlib bilateral infinite sum of formal series, and no such summation
operation or Laurent-series equality is asserted.

Pairing `m+1` with `-m-2` cancels the terms at `A = 0`. Each paired remainder
is divisible by four over the integers. Integral division by four gives a
degree-contracting iteration; stabilized coefficients construct the series,
and `generating_unique` proves uniqueness for the finite-window equation.

Modulo-sixteen linearisation and weighted telescoping use the unsigned frozen
`ThetaSelfCompositionModFour.thetaSeries` directly: multiplication by eight
removes the alternating signs modulo sixteen. `cancellation_identity` gives
`∃ Q : ℤ⟦X⟧, 1 = A*θ₃ + 4*Q`. Cancellation of four takes place over the
integers BEFORE reduction; cancellation inside `ZMod 4` would be invalid.
Since `θ̄₃ = 1 + 2*S̄` is self-inverse over `ZMod 4`, `mod_four_identity`
gives `Ā = θ̄₃`. Coefficient comparison proves `hanna_conjecture`: for
`n >= 1`, `a n % 4 = 2 ↔ IsSquare n` and
`a n % 4 = 0 ↔ ¬ IsSquare n`. `a_zero` gives `a 0 = 1`.

Target generality is I because the proof imports the frozen
`D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour`, itself generality G.

## Falsifier

A positive counterexample index at which either coefficient biconditional
fails would falsify the COMMENT. The orchestrator's exact arithmetic check is
supporting evidence only; the formal theorem quantifies over every positive
index.

## Evidence

- Lean module: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.lean`.
- Main theorem and sole resolution claim: `hanna_conjecture`.
- Companions: `bilateralTerm_coeff_eq_zero`, `generating_equation`,
  `generating_unique`, `a_zero`, `cancellation_identity`, `mod_four_identity`.
- Axioms: std3, namely `propext`, `Classical.choice`, `Quot.sound`, reported for
  each of the seven public theorems by the implementation seat.
- Frozen dependency statement_id:
  `sha256:0aec24647d5df63513f2c164c40043a38afc3ac9d0a739e594942fb5328c725b`.

The exact Lean cases, including the private definitions that expand them, are:

```lean
private noncomputable def positiveTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 1) * X ^ (m + 1) * (4 * A + X ^ m) ^ (m + 2)

private noncomputable def reciprocal (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  invOfUnit (1 + 4 * A * X ^ (m + 3)) 1

private noncomputable def negativeTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 2) * X ^ (m ^ 2 + 3 * m + 1) * reciprocal A m ^ (m + 1)

noncomputable def bilateralTerm (A : PowerSeries ℤ) (n : ℤ) : PowerSeries ℤ :=
  if n = 0 then 4 * A else if n = -1 then 0 else
    if 0 < n then positiveTerm A (n.toNat - 1) else negativeTerm A (-n - 2).toNat
```

The generating equation statement is quoted with its proof body omitted:

```lean
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N (4 : PowerSeries ℤ) =
      coeff N (∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm generatingSeries n) := by
```

These declarations express the finite-window interpretation of the NAME,
not an independently formalised analytic or bilateral infinite-sum identity.

## Triage

`theorem`. The formal proof closes both clauses of the COMMENT for the unique
integer series satisfying the stated coefficientwise interpretation of the NAME.

## ASSUMED-UNVERIFIED

The OEIS quotations and entry attribution were supplied by the orchestrator.
The OEIS entry and revision history were read by the search seat on 2026-09-09,
not by this network-disabled Stage-B seat. The literature search scope was
identifier searches on arXiv, MathOverflow, and GitHub; no exhaustive claim
about other indexes or unpublished proofs is made. First-publication priority
and identification of the OEIS NAME with the finite-window formal reading are
not kernel-checked facts. The orchestrator's exact check and external gate
results were supplied evidence, not executions by this seat.
