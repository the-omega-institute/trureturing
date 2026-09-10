---
slug: oeis-a220181-alternating-weight-stirling-prime-period
bibkey: bala2022a220181
doi: null
url: https://oeis.org/A220181
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod
---

# Prime periods of the A220181 alternating-weight Stirling sum

## Problem

OEIS A220181 gives the following NAME, finite FORMULA, and COMMENT, copied
verbatim from `Library/Recurrence/bala2022a220181.md`:

> E.g.f.: Sum_{n>=0} (1 - exp(-n*x))^n.

> a(n) = Sum_{k=0..n} (-1)^(n-k) * k^n * k! * Stirling2(n,k).

> Conjecture: Let p be prime. The sequence obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1. For example, modulo 7 the sequence becomes [1, 0, 3, 0, 0, 1, 1, 0, 3, 0, 0, 1 ...], with an apparent period of 6. Cf. A122399.

The entry is by Paul D. Hanna, Dec 06 2012; the conjecture COMMENT resolved
here is by Peter Bala, Jun 01 2022. The two attributions are recorded
separately rather than reassigning the comment to the entry author.

## Motivation

This is a first-tier OEIS conjecture: the entry dates from 2012 and the conjecture COMMENT from 2022.
KPI = open problems resolved. The target covers every prime and every positive
index, through a theorem for arbitrary integer weights.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching identifiers on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network and did not repeat
those searches. Failure to find a proof in that scope is not a priority claim.

## Route

The escape content is `aw_prime_period`: for an arbitrary integer weight
`w : ℕ → ℤ` and every prime `p`, the sequence
`aw w n = Σ_{k ≤ n} w k · kⁿ · k! · Stirling2(n,k)` satisfies
`aw w (n + (p - 1)) ≡ aw w n (mod p)` for `n ≥ 1`.

Its live proof has three steps. `aw_window` reduces to the fixed window `k < p`:
terms with `k ≥ p` vanish because `p ∣ k!`, and terms with `k > n` vanish because
`Stirling2(n,k) = 0`. `aw_exponential_sum` substitutes the frozen public
`stirling2_inclusion_exclusion`, obtaining a sum of `c(k,j) · (k*j : ZMod p)^n`
with coefficients independent of `n`. `pow_add_pred_prime` gives
`x^(n + (p - 1)) = x^n` in `ZMod p` for `n ≥ 1`: Fermat handles nonzero `x`,
while both sides vanish for zero `x`.

For A220181, `a_eq_alternating` proves
`a n = (-1)^n * aw (fun k => (-1)^k) n` from the finite FORMULA.
`bala_conjecture` transfers the period: `p - 1` is even for odd primes,
and the sign is trivial modulo 2. Target generality is I because the module
imports the frozen `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod`,
whose own generality is G.

## Falsifier

A prime `p` and an index `n ≥ 1` for which the finite FORMULA satisfies
`a(n + p - 1) ≢ a(n) (mod p)` would refute the conjecture.
The orchestrator's exact numerical check is supporting evidence only;
it does not replace the universally quantified proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.lean`.
- Main theorem: `bala_conjecture`. The requested name `hanna_conjecture` does
  not occur in the supplied Lean API; the single A220181 resolution claim
  binds the actual `bala_conjecture` declaration.
- Escape theorem: `aw_prime_period`, for arbitrary `w : ℕ → ℤ`. It is NOT an
  instantiation of any frozen public theorem: the frozen
  `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod` fixes `w = 1`
  (A122399), and the frozen
  `D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod` fixes
  `w k = 4^k` over `ℕ` (A338040). Source inspection showed that both expose
  their specialized `a_eq_window` publicly and keep `a_eq_double_sum` private.
  Thus the brief's assertion that both window helpers are private is inaccurate;
  neither specialized window nor either frozen period theorem states the
  arbitrary-integer-weight result.
- Companions: `aw`, `aw_window`, `aw_exponential_sum`, `pow_add_pred_prime`,
  `aw_prime_period_multiple`, `a`, `a_eq_alternating`, `bala_conjecture_periodic`.
- Frozen direct dependency statement_id:
  `sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
- Implementation-seat axiom report for all ten public declarations: std3,
  `[propext, Classical.choice, Quot.sound]`.
- The supplied search report records Bala's identical conjecture on A122399,
  A338040, A220181, A224899, A221077, and A195415. At the 2026-09-09 handoff,
  repository proofs covered the first three, including this implementation.
  A224899, A221077, and A195415 are NOT claimed here: their supplied e.g.f.
  shapes involve sinh and tanh powers, not weighted Stirling power sums.
  Exactly one resolution claim is made, for A220181.

## Triage

`theorem`. The formal proof establishes the stated period for the finite
FORMULA at every positive index; it does not assert a minimal period or
formalize the e.g.f. identity.

## ASSUMED-UNVERIFIED

The quotes and entry attribution were supplied by the orchestrator and copied
from the Library material as distinguished above. The OEIS revision history
was read by the search seat, not this seat. Literature scope was the OEIS
entry/history and identifier searches on arXiv, MathOverflow, and GitHub;
this seat had no network. The six-entry attribution and e.g.f. classification
come from the supplied search report. Source-to-Lean identification,
first-publication priority, and searches beyond that scope are not
kernel-checked facts. The e.g.f.-to-finite-formula identity is not formalized.
