---
slug: oeis-a365574-hanna-lagrange-parity-conjecture-1
bibkey: hanna2023a365574
doi: null
url: https://oeis.org/A365574
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.result
---

# Hanna's A365574 Lagrange parity conjecture

## Problem

Paul D. Hanna's [OEIS A365574](https://oeis.org/A365574) states:

> Expansion of g.f. A(x) satisfying [x^(n-1)] (1 + (n+1)*x*A(x))^n / A(x)^n = n*(n+2)^(n-2) for n > 1.

> Conjecture 1: a(k) is odd iff k = 2^n - 2 for n >= 1.

The literal binding conventions and source screen are in [#18829](https://github.com/the-omega-institute/trureturing/issues/18829). All series are formal; no analytic convergence is assumed.

### Statement echo

All unqualified names below belong to `D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity`.

| Source clause or binding convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| Normalization and every diagonal identity for $n>1$ | `IsGF` | Rational formal series, $A(0)=1$, and the literal coefficient expression are retained. |
| Odd exactly at $k=2^n-2$, $n\ge1$ | `claim`, `result` | Every natural $k$, including zero, has an integer coefficient witness and the biconditional. |
| Existence and integrality | `claim`, `result` | These rule out vacuity and supply the integer meaning of oddness; they add no hypothesis. |

## Motivation

This is an externally named tier-1 conjecture, preregistered in #18829. The single settling declaration is `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.result`, with the sole resolution claim for this dossier, `Proved`. Admission is `open-problem-resolution (#18829; Proved)` through `deposit-uncovered`, without an atom.

## Gap

The source and literature readings in #18829 found no proof within the stated searched scope. The research seat's entry-history readings are attributed to that seat; they are not an exhaustive novelty result. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The private integral construction `Core.RZ` is the rational expression $R=X(1-2X^2-2X^3)/((1-X)^2(1+2X)^2)$ formed over the integers. Mathlib's unit-linear reversion constructs `Core.HZ`, and `Core.AZ` removes its leading $X$. The rational images are `canonicalR` and `canonicalA`.

`Lagrange.inversion_coefficient` applies the frozen S3 supplier `NonnestingOneThreeTwoTwo.lagrange_coefficient`. The private Mobius identities and partial fractions give `Mobius.diagonal_coefficient`; `canonicalA_isGF` connects this calculation to the literal generating predicate. The strong induction in `solution_unique` determines each inverse coefficient from the earlier ones. `Core.mod_two_R`, `Core.mod_two_H` and the reused `UnitReversionSquareParity.lacunary_coeff` identify the odd support; `result` combines existence, uniqueness and coefficient parity.

## Falsifier

A solution of the literal generating predicate with a nonintegral coefficient or a coefficient violating the claimed odd-support biconditional would contradict `result`. The existence conjunct excludes vacuity.

## Evidence

- Lean owner: `D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.lean`; settling theorem: `D5.S3.Combinatorics.PowerSeries.HannaLagrangeParity.result`.
- Source note: `Library/RecurrenceComposition/hanna2023a365574.md`.
- Blueprint: `Blueprint/D5/S3/Combinatorics/PowerSeries/HannaLagrangeParity.md`.
- Classification: `result` has `proof_shape: content`; admission is the named open-problem resolution. The header records `escape_witness: none`; no validated escape registration is asserted.
- The four-slot audit is unfinished for both settling results and the published owner suppliers, under [#19951](https://github.com/the-omega-institute/trureturing/issues/19951). Complete-statement source reconstruction, an enrolled readout, intervention, sensitivity and observational-dependence evidence are missing.

### Declaration classifications

The same-delivery helpers are expanded for classification. Names are relative to the Lean owner.

| Declaration | proof_shape | Consumers |
| --- | --- | --- |
| `Core.AZ` | `bind-only` | `Core.AZ_constant, canonicalA, Core.X_AZ, canonical_reversion, Core.AZ_parity, canonicalA_constant, result` |
| `Core.AZ_constant` | `bind-only` | `canonicalA_constant` |
| `Core.AZ_parity` | `bind-only` | `result` |
| `Core.HZ` | `bind-only` | `Core.AZ_constant, Core.AZ, Core.X_AZ, canonical_reversion, Core.reversion, Core.mod_two_H, Core.AZ_parity, Core.HZ_one, Core.HZ_zero` |
| `Core.HZ_one` | `bind-only` | `Core.AZ_constant, Core.AZ_parity` |
| `Core.HZ_zero` | `bind-only` | `Core.X_AZ, canonical_reversion, Core.mod_two_H, Core.AZ_parity` |
| `Core.RZ` | `bind-only` | `canonicalR, Core.RZ_one, canonicalR_equation, canonical_reversion, Core.reversion, Core.mod_two_H, Core.mod_two_R, Core.HZ, Core.RZ_zero, Core.RZ_equation, Core.HZ_one, Core.HZ_zero` |
| `Core.RZ_equation` | `bind-only` | `canonicalR_equation, Core.mod_two_R` |
| `Core.RZ_one` | `bind-only` | `Core.HZ, Core.HZ_one, Core.HZ_zero, Core.reversion` |
| `Core.RZ_zero` | `bind-only` | `Core.reversion` |
| `Core.X_AZ` | `bind-only` | `canonical_reversion` |
| `Core.mod_two_H` | `bind-only` | `Core.AZ_parity` |
| `Core.mod_two_R` | `bind-only` | `Core.mod_two_H` |
| `Core.reversion` | `bind-only` | `canonical_reversion, Core.mod_two_H` |
| `IsGF` | `bind-only` | `solution_unique, canonicalA_isGF, claim, result` |
| `Lagrange.inversion_coefficient` | `bind-only` | `canonicalA_isGF` |
| `Mobius.diagonal_coefficient` | `bind-only` | `canonicalA_isGF` |
| `Mobius.geom_mul` | `bind-only` | `Mobius.geom_subst` |
| `Mobius.geom_square_coeff` | `bind-only` | `Mobius.diagonal_coefficient` |
| `Mobius.geom_subst` | `bind-only` | `Mobius.transformed_partial` |
| `Mobius.partial_fraction` | `bind-only` | `Mobius.transformed_partial` |
| `Mobius.subst_one` | `bind-only` | `Mobius.transformed_partial, shifted_reversion, Mobius.geom_subst` |
| `Mobius.subst_three` | `bind-only` | `Mobius.transformed_partial` |
| `Mobius.subst_two` | `bind-only` | `Mobius.transformed_partial` |
| `Mobius.transformed_partial` | `bind-only` | `Mobius.diagonal_coefficient` |
| `canonicalA` | `bind-only` | `canonical_reversion, canonicalA_isGF, canonicalA_constant, result` |
| `canonicalA_constant` | `bind-only` | `canonicalA_isGF` |
| `canonicalA_isGF` | `bind-only` | `result` |
| `canonicalR` | `bind-only` | `canonicalR_equation, canonical_reversion, canonicalA_isGF` |
| `canonicalR_equation` | `bind-only` | `canonicalA_isGF` |
| `canonical_reversion` | `bind-only` | `canonicalA_isGF` |
| `claim` | `bind-only` | `result` |
| `normalized_power` | `bind-only` | `solution_unique, canonicalA_isGF` |
| `result` | `content` | `settling result` |
| `shifted_reversion` | `bind-only` | `canonicalA_isGF` |
| `solution_unique` | `content` | `result` |

### Experiment

[Exact arithmetic checker and source data](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research), commit `9dfe5bdc210cac281a148e7180239ddb21b0b34b`. Command: `python3 check.py` in that directory; exit 0. Script SHA-256: `ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`. For A365574 the explicit reversion satisfies the defining identity for $2\le n\le19$; the first 12 source terms match, coefficients are integral, and Conjecture 1 holds for $0\le k\le59$. These are computed finite readings; the universal statement is the Lean result.

## Triage

| Lane target item | Status | Evidence |
| --- | --- | --- |
| Exact binding settlement | Proved | Kernel-checked `result`: existence and every coefficient clause. |
| A365574 Conjecture 2 modulo 16 | Open | The assertion $a(2^n-2)\equiv3\pmod {16}$ for $n>1$ is outside these two result statements. |
| A380711 odd-support/Fibbinary strengthening | Open in this delivery | The quotient congruence is settled; no separate theorem connects this source's coefficients to Fibbinary support. |
| Reuse the Lagrange supplier outside Recurrence | Proved interface use | Kernel-checked private `HannaLagrangeParity.Lagrange.inversion_coefficient` directly applies `D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient`. No additional inversion theorem is asserted. |
| Finite arithmetic evidence | Computed | The pinned experiment and exact tested scope above. |
| Literature completeness | Open | `ASSUMED-UNVERIFIED`, bounded by the screen in #18829. |

### What the settlement shows

**Kernel-checked:** `result` supplies a normalized series and integrality and exact odd support for every normalized rational solution. The private `solution_unique` proves that solution is unique. The decisive step is the triangular inverse-coefficient induction, combined with the reduction of the integral reversion to $X/(1+X^2)$ modulo two.

**Explanation:** the explicit rational reversion is a representation of the solution via compositional inversion. This delivery gives no additional theorem that derives Fischer's quartic equation from the source identity. That derivation, Conjecture 2 modulo 16, and any analytic convergence assertion remain open here. The support includes $k=0$ because $2^1-2=0$.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not Lean conclusions. The finite experiment does not prove the unbounded claim. The four-slot escape audit remains unfinished under #19951. The source's separate unsettled questions retain their stated boundaries above.
