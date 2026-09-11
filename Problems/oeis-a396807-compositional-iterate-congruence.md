---
slug: oeis-a396807-compositional-iterate-congruence
bibkey: hanna2026a396807
doi: null
url: https://oeis.org/A396807
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CompositionalIterateCongruence
---

# Coefficient congruence for OEIS A396807

## Problem

NAME "G.f. satisfies A(x) = x + A^5(x)*A^6(x)." where A^n(x) denotes the n-th iteration (compositional power) of A(x).

COMMENT "Conjecture: a(n) = 1 (mod 10) for n >= 1." — Paul D. Hanna, Jun 16 2026.

## Motivation

This is a first-tier 2026 OEIS conjecture. The KPI is open problems resolved:
the target is the congruence for every positive index, without a finite cutoff.

## Gap

The orchestrator reported no proof found in its 2026-09-08 search of the OEIS
entry/history and identifier searches on arXiv, MathOverflow, and GitHub.
This seat did not read the OEIS revision history or independently repeat those
network searches. This is a bounded literature-search report, not a claim of
exhaustive priority verification.

## Route

For zero-constant series over any commutative ring, the transformation
`A ↦ X + A∘5 · A∘6` improves coefficient agreement by one degree. Induction
therefore gives coefficientwise uniqueness. Picard approximations starting
from zero stabilize degree by degree and construct the integer solution.

Over `ZMod 10`, the series `X/(1-X)` has k-th compositional iterate
`X/(1-kX)`. The identity `(1-5X)(1-6X) = 1-X` modulo ten shows that
`X/(1-X)` satisfies the equation. These denominators are units of the formal
power-series ring; no field hypothesis is needed. Map the integer solution
to `ZMod 10` and apply uniqueness. Every positive coefficient is then one
modulo ten.

## Falsifier

An index `n ≥ 1` with `a(n) mod 10 ≠ 1` would falsify the assertion.
The orchestrator reported recomputing `a(1..12)` with termwise agreement with
OEIS and obtaining residue one for every `1 ≤ n ≤ 22`. These finite checks
support source identification; they do not replace the unbounded proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.lean`.
- Main public theorem: `coefficient_congruence`.
- Supporting public theorems: `generating_equation`, `fixed_unique`,
  `mod_ten_fixed`, and `mobius_iterate`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all five
  public theorems, as recorded in the implementation seat's `print_axioms`
  report.

## Triage

`theorem`. The formal proof establishes the positive-index congruence for the
constructed sequence and characterizes its generating series uniquely by the
zero-constant OEIS equation.

## ASSUMED-UNVERIFIED

The Lean sequence uses an explicit Picard-approximation coefficient definition:
`approximation 0 = 0`, `approximation (d+1) = step (approximation d)`, and
`a n = coeff n (approximation (R := ℤ) (n+1))`. Its generating series is
`mk a`. The public theorem `generating_equation` states exactly:

```lean
theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    generatingSeries = X + iterate generatingSeries 5 * iterate generatingSeries 6
```

Thus it proves both zero constant coefficient and the generating equation
for this explicit series; it assumes neither existence nor the congruence.
Uniqueness is a separate conclusion supplied by `fixed_unique`, applied to
zero-constant fixed points. Identifying this characterized sequence with the
OEIS entry relies on the supplied source definition, not on a kernel-checked
copy of the external page or a finite-data theorem.

This seat did not read the OEIS revision history. The quotes, attribution,
date, and finite computations were supplied by the orchestrator. Literature
scope was the orchestrator's 2026-09-08 OEIS entry/history and identifier
searches on arXiv, MathOverflow, and GitHub; no proof was reported in that
scope, and exhaustive literature coverage or first-publication priority was
not established.
