---
slug: oeis-a221077-tanh-power-prime-period
bibkey: bala2022a221077
doi: null
url: https://oeis.org/A221077
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod
---

# Refutation of the all-prime A221077 period conjecture

## Problem

OEIS A221077 (Paul D. Hanna's entry) specifies the following NAME. The
Library note records Peter Bala's conjecture dated Jun 01 2022; that date
and attribution belong to the conjecture, not to an asserted entry-creation date.
The following NAME and COMMENT are quoted verbatim from the supplied Library note.

NAME:

> E.g.f.: Sum_{n>=0} tanh(n*x)^n.

COMMENT (Peter Bala, Jun 01 2022):

> Conjecture: Let p be prime. The sequence obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1. For example, modulo 7 the sequence becomes [1, 1, 6, 1, 0, 4, 1, 1, 6, 1, 0, 4, 1, 1, 6, 1, 0, 4 ...], with an apparent period of 6.

This is one conjecture quantified over all primes. It is false at p = 2;
its substantive period assertion survives for every odd prime.

## Motivation

This is a first-tier OEIS conjecture recorded in the entry in 2022. The KPI
is open problems resolved: the all-prime assertion is refuted, and the
accompanying odd-prime theorem delimits exactly where the asserted period
holds. No repository cumulative KPI is claimed.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat those source or literature checks. Absence of a
located proof is limited to that search scope.

## Route

The exact positive-integer closed form
`a(n) = Σ_{m=1..n} 2^{n−m}·m!·(m−1)!·S(n,m)·S(n+1,m)`
is the escape content. It removes the tanh denominator and exposes two
factorials. Modulo an odd prime p, terms with `m ≥ p` die because `p ∣ m!`,
and terms with `m > n` die because `S(n,m) = 0`. The sum therefore collapses
to the fixed range `1 ≤ m < p`, as proved by `a_window`.

Expanding both Stirling factors by inclusion–exclusion gives
`a_exponential_sum`, a fixed triple sum with base `2·j·k` and coefficients
independent of n. The frozen
`D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.pow_add_pred_prime`
finishes the proof of `bala_conjecture_odd`, including zero bases for n ≥ 1.

The exponential-sum step needs 2 to be invertible, locating the exceptional
prime p = 2. The module proves `¬ bala_conjecture_two` via
`bala_conjecture_two_false`: a(1) = 1 and a(2) = 8 have different parity,
so period p−1 = 1 fails. The failure is confined to p = 2. Thus the entry's
single conjecture is refuted, with its substantive odd-prime content proved.

Target generality is I. Lean defines a by the closed form; the bridge from
the e.g.f. to that formula is derived in the Library note, not formalized.
This source-identification boundary also applies to the resolution claim.
OEIS A195415 is not claimed: the integrality bridge `4^(n−1) ∣ a(n)` does
not follow term by term. The asserted period need not be minimal.

## Falsifier

The counterexample is p = 2 at index n = 1: the claimed equality compares
a(2) = 8 with a(1) = 1 modulo 2. Period one would require constancy from
n = 1. This is the formal refutation witness. The orchestrator's exact
numerical check is supporting evidence only, not a substitute for the
refutation certificate or the universal odd-prime proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.lean`.
- Resolution theorem: `bala_conjecture_two_false : ¬ bala_conjecture_two`;
  the sole resolution claim has kind `Refuted` and binds to this theorem.
- Accompanying positive theorem: `bala_conjecture_odd`, for every prime
  p ≠ 2 and every n ≥ 1. Companions: `a_window`, `a_exponential_sum`.
- The module has no declaration named `hanna_conjecture`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported
  for all six public declarations by the implementation seat.

## Triage

`theorem`. One all-prime conjecture is resolved by refutation at p = 2;
the positive odd-prime theorem precisely delimits its surviving content.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from
`Library/Recurrence/bala2022a221077.md`. The OEIS entry and revision history
were read by the search seat on 2026-09-09, not by this network-disabled
Stage-B seat. The reported literature scope was identifier searches on
arXiv, MathOverflow, and GitHub; it was not an exhaustive literature review.
Attribution, first-publication priority, and identification of the closed
form with the OEIS e.g.f. are not kernel-checked facts. The Library note
supplies a prose derivation of that identification.
