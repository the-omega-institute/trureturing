---
slug: oeis-a064618-stirling-transform-totient-period
bibkey: bala2018a064618
doi: null
url: https://oeis.org/A064618
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod
---

# A064618 totient-period conjecture

## Problem

OEIS A064618 NAME:

> Stirling transform of (n!)^2.

OEIS A064618 COMMENT (Peter Bala, Jan 15 2018):

> Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is eventually periodic with the exact period dividing phi(k), where phi(k) is the Euler totient function A000010.

The finite formula for this entry is `a(n) = T (fun k => (k.factorial : ℤ)) n`; its proved onset is `n ≥ m`
for every positive modulus `m`. The entry has offset 0.

The companion entry is recorded separately with its own Library note and dossier:

A004123 NAME (offset 1):

> Number of generalized weak orders on n points.

A004123 COMMENT (Peter Bala, Jul 08 2022):

> Conjecture: Let k be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).

## Motivation

This is a first-tier OEIS conjecture recorded in 2018. The target resolves the
entry's totient-period assertion for every positive modulus. KPI: open problems
resolved; no repository cumulative count is claimed.

## Gap

No proof was found in the search seat's reported search: OEIS entry and revision
history read on 2026-09-09, plus identifier searches on arXiv, MathOverflow, and
GitHub. This Stage-B seat had no network access and did not independently
verify that literature search. The formal argument must handle arbitrary
integer weights and composite moduli, including non-unit bases.

## Route

The escape content is `stirling_transform_totient_period`: for an arbitrary
weight `w : ℕ → ℤ` and any modulus `m ≥ 1`, the integer transform
`T w n = Σ_{k≤n} w(k) · k! · S(n,k)` satisfies
`T w (n + φ(m)) ≡ T w n (mod m)` whenever `n ≥ m`. Target generality: I.

Its live proof path has three steps. `T_window` collapses the sum to the fixed
range `k < m`: terms with `k ≥ m` vanish because `m ∣ k!`, and terms with
`k > n` vanish because `S(n,k) = 0`. `T_exponential_sum` rewrites that window
by inclusion-exclusion as a fixed integer combination of `jⁿ`.
`pow_add_totient` supplies the prime-power split: for each prime power `q = p^e`
dividing `m`, a unit base uses Euler's theorem together with `φ(q) ∣ φ(m)`;
a non-unit base has both powers vanishing once the exponent reaches `e`.
The bound `e < p^e ≤ m ≤ n` supplies this vanishing and explains the sufficient
onset `n ≥ m`. Prime-power divisibility combines the local congruences for
composite `m`.

This general theorem is a sibling of the frozen modules
`D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod` and
`D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod`, not an instance
of either: their summand carries an extra `kⁿ`, and their period conclusions
cover only prime moduli. The proof directly imports the former for its public
`stirling2_inclusion_exclusion` lemma; the latter is a comparison sibling.

The named instances are `bala_conjecture_a064618` at `w k = (k! : ℤ)` and
`bala_conjecture_a004123` at `w k = 2 ^ k`. A004123 has offset 1:
`a(n) = T (fun k => (2 : ℤ)^k) (n - 1)` for `n ≥ 1`, so its guard is
`n ≥ m + 1`. Neither the onset nor the period is asserted to be minimal.
A004123 also carries a broader conjecture about every e.g.f. of the form
`G(exp(x) − 1)`; this PR does not claim that broader conjecture.

## Falsifier

A positive modulus `m` and an entry index `n` satisfying `n ≥ m` with
`a(n + φ(m))` not congruent to `a(n)` modulo `m` would falsify the formal
entry assertion. A failure below that sufficient onset would not do so.
To refute eventual periodicity itself would require failures beyond every
possible onset for a fixed modulus. The orchestrator's exact finite check
is supporting evidence only.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.lean`.
- Main entry theorem: `bala_conjecture_a064618`.
- General theorem: `stirling_transform_totient_period`.
- Companions: `T`, `T_window`, `T_exponential_sum`, `pow_add_totient`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for `T` and all six public theorems.

The orchestrator reported from `results/verify-r17.out` that both finite
formulas reproduced the published DATA exactly and that periodicity had zero
violations for every modulus `1 ≤ m ≤ 48` over `n < 64`, subject to the
respective onset guards. These finite checks are supporting evidence, not
proof; this seat did not independently read that output.

## Triage

`theorem`. The named entry theorem proves the totient-period assertion via the
arbitrary-weight theorem. The broader A004123 e.g.f. conjecture is not claimed.

## ASSUMED-UNVERIFIED

The OEIS quotations and source attributions were supplied by the orchestrator.
The search seat, not this Stage-B seat, read the OEIS entries and revision
histories on 2026-09-09 and searched identifiers on arXiv, MathOverflow, and
GitHub. This seat had no network access and did not repeat those searches.
No proof was found within that reported scope; this is not an exhaustive
literature or first-publication-priority claim. Source-to-Lean identification
and the orchestrator's finite-check readings are not kernel-checked facts.
The standard axiom report (std3: `propext`, `Classical.choice`, `Quot.sound`)
was supplied by the implementation seat; Stage B did not rerun Lean.
