---
slug: oeis-a094802-perry-least-factorial-divisible-by-prefix-lcm
bibkey: perry2004a094802
doi: null
url: https://oeis.org/A094802
triage: theorem
motivation_gids:
  - D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.result
  - D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.prefix_lcm_dvd_factorial_of_maximal_prime
---

# Perry's A094802 least factorial index conjecture

## Problem

The OEIS entry states, verbatim:

> %N A094802 a(n) = smallest k such that all of 1 through n divides k!.
> %C A094802 It is conjectured that after n=4 the sequence is prime for n prime or the previous prime for n not prime.
> %A A094802 _Jon Perry_, Jun 11 2004
> %O A094802 1,2

The literal proved statement is: for all natural n and p, if `5 <= n`,
`Nat.Prime p`, `p <= n`, and every prime q at most n satisfies `q <= p`,
then `IsLeast {k : Nat | Nat.lcmUpto n | k !} p`. For a prime n, p is n;
otherwise it is the previous prime. Thus p is precisely the largest prime
at most n. The entry's example `a(6)=5 as 5!=120 which is divisible by
1,2,3,4,5 and 6.` agrees. The bound is necessary: `a(4)=4` is not prime.
Mathlib defines `Nat.lcmUpto n` as `(Finset.Icc 1 n).lcm id`, so the `%N`
divisibility clause is precisely `Nat.lcmUpto n | k !`.

Not claimed: a general formula for n at most four beyond the computed
values, any general theorem about the Kempner function away from this
prefix-lcm input, or an asymptotic estimate for `lcmUpto`.

## Motivation

Jon Perry's conjecture dates from June 2004. Revision #1 (September 2004)
already contains the conjecture, and revision #10 (2024-04-01) still marks
it as a conjecture without a settlement comment. It evaluates the
Kempner/Smarandache function at the specific input `lcm(1,...,n)`.

## Gap

The current OEIS revision #10 (Apr 01 2024 12:14:58) has no closed-form
`%F`, no `%H` reference link, and no settlement comment. Its other content
comprises programs, one example, `%Y Cf. A002034, A007917`, and `%E
Corrected by T. D. Noe, Nov 02 2006`. The ten-revision history includes
the conjecture already in #1 (N. J. A. Sloane, Sep 22 2004).

The probe read Jon Perry's own 2004 paper *Calculating the Smarandache
Numbers* in full: it derives an exact prime-factor algorithm for the
Kempner/Smarandache function, but neither states nor proves this prefix-lcm
largest-prime claim. The cross-referenced A002034 gives general prime-factor
algorithms without an A094802 citation or evaluation at `lcm(1,...,n)`.
A007917 identifies the largest prime at most n as the largest prime dividing
that lcm but does not assert that the Kempner value of the lcm is that prime.
Crossref queries for `Kempner function lcm`, `Smarandache function lcm`,
`S(lcm(1,...,n))`, and `smallest factorial divisible by the least common
multiple` returned no relevant settlement. This is
`not-found-in-searched-scope`, not an exhaustive search or priority claim.

## Route

The lower bound observes that a prime p at most n divides `lcmUpto n`;
for any admissible k it therefore divides `k!`, and
`Nat.Prime.dvd_factorial` forces `p <= k`. For the upper bound, Bertrand
gives a prime strictly between p and 2p, so maximality forces `n < 2p`.
Every m at most n either lies below p or is a nonprime between p and 2p.
The nonprime is split by its smallest prime factor: nonsquares embed their
two factors in `p!`; squares use two factorial blocks, with the small
squares 4 and 9 handled separately and a further Bertrand estimate for
larger squares. This is the non-reductive Legendre-style per-prime-power
factorial estimate, implemented through elementary divisibility rather
than a call to the Legendre formula. Mathlib's
`Nat.factorization_lcmUpto` supplies an alternative prime-power reading;
the proof itself unfolds `lcmUpto` and uses `Finset.lcm_dvd_iff` to
verify all its divisors directly.

## Falsifier

A natural n at least five and a maximal prime p at most n with
`lcmUpto n` failing to divide `p!` would contradict the reusable lemma.
An admissible index k less than p would contradict `result`.

## Evidence

- Lean: `D5/S3/Factorization/PerryLeastFactorialDivisibleByPrefixLcm.lean`.
- Both public theorems `prefix_lcm_dvd_factorial_of_maximal_prime` and
  `result` have std3 axiom closure `[propext, Classical.choice, Quot.sound]`.
- Kernel profile: wall 17.69 s, type checking 84.9 ms, maximum resident
  set size 2,741,731,328 bytes on this worktree.
- Independently deleting `Mathlib.NumberTheory.Bertrand` and
  `Mathlib.NumberTheory.Chebyshev` causes `lake env lean` exit 1 each.
- The probe reconstructed the literal `%N` by exact-integer incremental
  evaluation for `n=5..1000000` with a sieve of 78498 primes:
  `mismatches=[] count=0`. For `n=1..10`, values are
  `[1,2,3,4,5,5,7,7,7,7]`; the largest primes for `n=5..10` are
  `[5,5,7,7,7,7]`. Finite checks are not the universal proof.

## Triage

`theorem`: the maximal prime is the least factorial index for every
`n >= 5`. The resolution kind is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness remains unverified outside the named paper,
OEIS entries and revisions, Crossref shape queries, arXiv HTML and the
named benchmark paper, the repository, and pinned Mathlib. OpenAlex
returned HTTP 429 on all five requests, Semantic Scholar HTTP 429 on all
three, and the arXiv export API HTTP 429. Google Scholar required an
interactive browser unavailable to the probe. Those four surfaces remain
unchecked; no exhaustive literature or priority claim is made.
