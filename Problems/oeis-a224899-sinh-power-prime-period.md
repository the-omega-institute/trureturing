---
slug: oeis-a224899-sinh-power-prime-period
bibkey: bala2022a224899
doi: null
url: https://oeis.org/A224899
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod
---

# The prime-period conjecture for OEIS A224899

## Problem

OEIS A224899, NAME:

> E.g.f.: Sum_{n>=0} sinh(n*x)^n.

COMMENT (Peter Bala, May 29 2022):

> Conjecture: Let p be prime. The sequence obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1. For example, modulo 7 the sequence becomes [1, 1, 2, 0, 3, 0, 1, 1, 2, 0, 3, 0, ...], with an apparent period of 6. Cf. A245322.

The Library note attributes the entry to Paul D. Hanna, April 20, 2013,
and the conjecture to Peter Bala, May 29, 2022. The conjecture quantifies over
all primes. It is false at p = 2; its substantive content survives for every
odd prime, so the failure is confined exactly to p = 2.

## Motivation

This is a first-tier OEIS conjecture: entry year 2013, conjecture year 2022.
KPI = open problems resolved. The resolution refutes the all-primes statement
and proves the accompanying unrestricted odd-prime assertion.

## Gap

The supplied search report found no proof: the search seat read the OEIS
entry and revision history on 2026-09-09 and searched the identifier on
arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access and
did not independently repeat those searches. No proof found within that
scope does not establish exhaustive absence or publication priority.

## Route

The escape content is the coefficient bridge
`H(n,k) = kⁿ·k!·Σ_{r=k..n} C(n,r)(−k)^{n−r}2^{r−k}S(r,k)`
for the coefficient expression `H(n,k) = n![xⁿ] sinh(kx)^k`. It exposes the
factorial hidden in the raw exponential expansion, giving `k! ∣ H(n,k)`
and `H(n,k) = 0` for `k > n`. The Lean bridge sums over `0 ≤ r ≤ n`;
the extra terms with `r < k` vanish. The analytic e.g.f. identity itself
is not formalized: `H` and `a` start from the finite coefficient formula.

These two vanishing facts collapse the sum modulo p to the fixed window
`0 ≤ k < p` (`a_window`, including n = 0). For n ≥ 1, the k = 0 term
vanishes, leaving `1 ≤ k < p`. For odd p, `a_exponential_sum` exposes
coefficients independent of n. The frozen
`D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.pow_add_pred_prime`
then gives `bala_conjecture_odd`. The target generality is I; p−1 is a
period, not necessarily the least period.

The same analysis identifies the exception: the exponential-sum step needs
2 to be invertible. At p = 2 the claimed period is 1, but a(1) = 1 and
a(2) = 8 have different residues. `bala_conjecture_two_false` proves
`¬ balaConjectureTwo`. Thus the entry's single conjecture is refuted exactly
at p = 2, with its odd-prime content proved.

## Falsifier

The counterexample index is n = 1 at p = 2: a(1 + (2−1)) = a(2) = 8 is
even, whereas a(1) = 1 is odd. The orchestrator's exact numerical check is
supporting evidence only; the formal refutation evaluates these definitions
inside the proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.lean`.
- Resolution theorem: `bala_conjecture_two_false : ¬ balaConjectureTwo`;
  the single Scribe claim is `ResolutionKind.Refuted` on this theorem.
- Accompanying positive theorem: `bala_conjecture_odd`, for every odd prime
  and every n ≥ 1, precisely delimiting where the conjecture is true.
- Companions: `coefficient_bridge`, `a_window`, and `a_exponential_sum`;
  definitions: `H`, `a`, and `balaConjectureTwo`.
- The supplied module has no declaration named `hanna_conjecture`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported
  by the implementation seat's `#print axioms` checks.

## Triage

`theorem`. The all-primes conjecture is refuted at p = 2. The accompanying
odd-prime theorem preserves the entry's substantive content for every other
prime. There is one dossier and one refutation claim.

## ASSUMED-UNVERIFIED

The verbatim quotes and source attribution were supplied by the orchestrator
through `Library/Recurrence/bala2022a224899.md`. The OEIS revision history was
read by the search seat, not by this offline Stage-B seat. The supplied
literature scope was the OEIS entry and history plus identifier searches on
arXiv, MathOverflow, and GitHub on 2026-09-09; exhaustive literature coverage
and first-publication priority are not asserted. Identification of the finite
coefficient formula with the analytic e.g.f. is not kernel-checked.
