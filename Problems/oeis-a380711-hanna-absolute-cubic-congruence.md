---
slug: oeis-a380711-hanna-absolute-cubic-congruence
bibkey: hanna2025a380711
doi: null
url: https://oeis.org/A380711
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.result
---

# Hanna's A380711 absolute cubic congruence

## Problem

Paul D. Hanna's [OEIS A380711](https://oeis.org/A380711) states:

> G.f. A(x) satisfies A(x) = 1 + x*A(x)*abs( 1/A(x)^3 ).

> Conjecture: a(n) == binomial(3*n-1,n)/(3*n-1) (mod 2) for n >= 0.

The literal binding conventions and source screen are in [#18828](https://github.com/the-omega-institute/trureturing/issues/18828). All series are formal; no analytic convergence is assumed.

### Statement echo

All unqualified names below belong to `D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence`.

| Source clause or binding convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| Coefficientwise absolute value | `absSeries` | The coefficient of degree $n$ is the absolute value of the original rational coefficient. |
| The generating equation | `IsGF` | The displayed source equation is retained literally over rational formal power series. |
| Generalized binomial quotient | `quotient` | `Ring.choose` uses the integer top argument $3n-1$ and rational division; at zero the quotient is $-1$. |
| Congruence for every $n\ge0$ | `claim`, `result` | Integer witnesses represent both rational operands and satisfy `Int.ModEq 2`. |
| Existence and integrality | `claim`, `result` | These strengthen the literal congruence's interpretation without adding hypotheses. |

## Motivation

This is an externally named tier-1 conjecture, preregistered in #18828. The single settling declaration is `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.result`, with the sole resolution claim for this dossier, `Proved`. Admission is `open-problem-resolution (#18828; Proved)` through `deposit-uncovered`, without an atom.

## Gap

The source and literature readings in #18828 found no proof within the stated searched scope. The research seat's entry-history readings are attributed to that seat; they are not an exhaustive novelty result. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The private maps `stepZ` and `stepQ` increase coefficient agreement by one degree. `integer_exists` and `solution_unique` directly apply the frozen `PowerSeriesNormalizedContraction.exists_unique_fixed` through consumed adapters. `isGF_iff` connects these fixed points to the literal source equation.

`map_absZ` uses `AbsoluteReciprocalSquareParity.map_abs` to eliminate absolute value modulo two. `integral_reduction` identifies the result with the frozen square-shift series through its cubic equation. For positive indices, `quotient_integer` uses `AbsoluteReciprocalSquareShiftParity.ternary_dvd`, and `result` directly applies that owner's `hanna_conjecture`. At zero the generalized-binomial quotient is $-1$ and the series coefficient is $1$, which are congruent modulo two.

## Falsifier

A solution of the literal generating predicate with a nonintegral coefficient or a coefficient violating the claimed quotient congruence would contradict `result`. The existence conjunct excludes vacuity.

## Evidence

- Lean owner: `D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.lean`; settling theorem: `D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence.result`.
- Source note: `Library/RecurrenceComposition/hanna2025a380711.md`.
- Blueprint: `Blueprint/D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.md`.
- Classification: `result` has `proof_shape: bind-only`; admission is the named open-problem resolution. The header records `escape_witness: none`; no validated escape registration is asserted.
- The four-slot audit is unfinished for both settling results and the published owner suppliers, under [#19951](https://github.com/the-omega-institute/trureturing/issues/19951). Complete-statement source reconstruction, an enrolled readout, intervention, sensitivity and observational-dependence evidence are missing.

### Declaration classifications

The same-delivery helpers are expanded for classification. Names are relative to the Lean owner.

| Declaration | proof_shape | Consumers |
| --- | --- | --- |
| `IsGF` | `bind-only` | `isGF_iff, solution_unique, claim, result` |
| `absSeries` | `bind-only` | `stepQ, map_stepZ, isGF_iff, solution_unique, IsGF, stepQ_contract, map_absZ` |
| `claim` | `bind-only` | `result` |
| `integer_exists` | `bind-only` | `result` |
| `integral_reduction` | `bind-only` | `result` |
| `isGF_iff` | `bind-only` | `solution_unique, result` |
| `map_absZ` | `bind-only` | `map_stepZ` |
| `map_stepZ` | `bind-only` | `result` |
| `quotient` | `bind-only` | `quotient_integer, claim, result` |
| `quotient_integer` | `bind-only` | `result` |
| `result` | `bind-only` | `settling result` |
| `solution_unique` | `bind-only` | `result` |
| `stepQ` | `bind-only` | `map_stepZ, isGF_iff, solution_unique, stepQ_contract, result` |
| `stepQ_contract` | `bind-only` | `solution_unique` |
| `stepZ` | `bind-only` | `integral_reduction, stepZ_contract, map_stepZ, integer_exists, result` |
| `stepZ_contract` | `bind-only` | `integer_exists` |

### Experiment

[Exact arithmetic checker and source data](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research), commit `9dfe5bdc210cac281a148e7180239ddb21b0b34b`. Command: `python3 check.py` in that directory; exit 0. Script SHA-256: `ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`. For A380711 the first 12 source terms match, coefficients are integral, and the quotient is integral and congruent to the series coefficient for $0\le n\le40$. These are computed finite readings; the universal statement is the Lean result.

## Triage

| Lane target item | Status | Evidence |
| --- | --- | --- |
| Exact binding settlement | Proved | Kernel-checked `result`: existence and every coefficient clause. |
| A365574 Conjecture 2 modulo 16 | Open | The assertion $a(2^n-2)\equiv3\pmod {16}$ for $n>1$ is outside these two result statements. |
| A380711 odd-support/Fibbinary strengthening | Open in this delivery | The quotient congruence is settled; no separate theorem connects this source's coefficients to Fibbinary support. |
| Reuse the Lagrange supplier outside Recurrence | Proved interface use | Kernel-checked private `HannaLagrangeParity.Lagrange.inversion_coefficient` directly applies `D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient`. No additional inversion theorem is asserted. |
| Finite arithmetic evidence | Computed | The pinned experiment and exact tested scope above. |
| Literature completeness | Open | `ASSUMED-UNVERIFIED`, bounded by the screen in #18828. |

### What the settlement shows

**Kernel-checked:** `result` supplies a solution and proves both operand integrality and their congruence for every rational solution and every natural index. The private `solution_unique` proves uniqueness. Absolute value disappears on reduction modulo two, and the frozen cubic comparison supplies the quotient congruence.

**Proved in prose from the definitions:** the zero-index representative of the quotient is $-1$, not the positive-index natural quotient expression; it remains congruent to the constant series coefficient $1$. The positive-index restriction in `quotient_integer` is therefore retained. The separate Fibbinary classification, convergence radius and asymptotic constants in the source are not conclusions of this theorem.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not Lean conclusions. The finite experiment does not prove the unbounded claim. The four-slot escape audit remains unfinished under #19951. The source's separate unsettled questions retain their stated boundaries above.
