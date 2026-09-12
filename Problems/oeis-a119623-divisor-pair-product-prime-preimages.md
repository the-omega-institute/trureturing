---
slug: oeis-a119623-divisor-pair-product-prime-preimages
bibkey: seidov2006a119623
doi: null
url: https://oeis.org/A119623
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages
---

# Prime values of the divisor-pair product sum have exactly two preimages

## Problem

OEIS A119623, NAME (Zak Seidov, Jun 08 2006):

> Composite numbers for which the second elementary symmetric function of divisors (s2) is prime.

OEIS A119623, COMMENTS (Zak Seidov, Jun 08 2006):

> Terms in A119616 are always prime if n is prime p and s2(p)=p, hence it is interesting to find composite numbers for which s2 is also prime. Relative values of s2 are: s2=47,97,163,457,733,2203,3733,7993,10723,11317,21313,22147,26557,33403,57283,61417,67153,79393,101467,149323,160453,162727,174337,272683,296827,318793,358273,432907,440383,486583,551767,639007,832687,843043,911917,961183,1152913,1202017,1277593,1322743,1375303,1462897,1567327,1824997,1878883. Otherwise the sequence s2 gives numbers which appear in A119616 at least twice (and conjecture is that exactly twice).

OEIS A119616, NAME:

> Second elementary symmetric function of divisors of n.

Accordingly, `S2(n)` is defined here verbatim as `e_2(divisors(n))`, the
second elementary symmetric function of the finite divisor multiset. Lean's
`Nat.divisors 0` is empty, so this definition gives `S2(0)=0`. For positive
`n`, it is equivalently the sum of `d*e` over unordered pairs of distinct
divisors, or `(sigma_1(n)^2 - sigma_2(n))/2` as recorded in A119616 %F; these
are equivalent descriptions, not the adopted definition.

The adopted reading is: for every composite `n` for which `p = S2(n)` is
prime, `{m >= 1 : S2(m) = p} = {n, p}`. This is the only reading consistent
with both "at least twice" and "exactly twice": the identity `S2(p) = p`
provides the second occurrence, while "exactly" excludes every other
positive preimage.

## Motivation

This is a first-tier OEIS conjecture explicitly recorded in 2006. Proving the
full preimage classification resolves the published claim rather than only
checking the displayed sequence values.

## Gap

The preregistration search on 2026-09-13 checked all four revisions of
A119623, the full A119616 history, and exact identifiers on arXiv, OpenAlex,
MathOverflow, and GitHub commits and issues. A proof or counterexample was
not found in the checked surfaces. GitHub code search, Google Scholar, and
MathSciNet were not verified in that search.

## Route

Starting from the verbatim definition `S2(n)=e_2(divisors(n))`, the module
internally proves the equivalent divisor identity
`2*S2(n) = sigma_1(n)^2 - sigma_2(n)` from A119616 %F. For positive `n`, the
same definition is also the sum of `d*e` over unordered pairs of distinct
divisors. If a prime power `p^a` with `a >= 2` divides `n`, the two sigma
values have a common factor: for even `a` use `sigma_1(p^a)`; for odd `a`
and odd `p` use `1+p^2+...+p^(a-1)`; for `p=2` and odd `a` use
`(2^(a+1)-1)/3`. The factor is too large and too small to be compatible with
prime `S2(n)`, so `n` is squarefree.

For squarefree `n` with at least two odd prime factors, parity forces `S2(n)`
to be composite. The all-odd case uses the parity of `C(2^k,2)`. For
`n=2t`, the identity `S2(2t)=5*e_2(D(t))+2*sigma_1(t)^2` and the evenness of
`e_2(D(t))` give the same contradiction. Hence every composite `n` with
prime `S2(n)` is `2q` for an odd prime `q`.

Finally, `S2(2q)=2q^2+9q+2`, and this polynomial is strictly increasing on
the natural numbers. Together with `S2(p)=p` for primes and `S2(1)=0`, this
leaves exactly the composite argument and its prime value as preimages.

## Falsifier

A composite `n > 1` with prime `S2(n)` that is not twice an odd prime would
refute the classification lemma. A natural `m` satisfying `S2(m)=S2(n)` but
neither `m=n` nor `m=S2(n)` would refute the main theorem. Failure of
`S2(p)=p`, the formula for `S2(2q)`, or its strict increase would also break
the proof route.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.lean`.
- Public definition: `S2 n := n.divisors.val.esymm 2`, matching A119616 %N;
  `Nat.divisors 0` is empty and therefore `S2 0 = 0`.
- The pair-product sum and `2*S2(n) = sigma_1(n)^2 - sigma_2(n)` are
  equivalent descriptions from A119616 %F; the latter is proved internally,
  without a public bind-only identity theorem.
- Classification theorem: `eq_two_mul_prime_of_composite_of_s2_prime`.
- Resolution theorem: `seidov_conjecture`.
- Both theorem axiom closures are std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator's sieve through 3,000,000 found 11,857 qualifying
  composites, all of the form `2q`, and no preimage collisions.
- The probe independently checked through 300,000 and found 1,768 qualifying
  composites, all of the form `2q`, with no preimage collisions and no
  failures of the divisor identity.

## Triage

`theorem`. The formal statement quantifies over every natural preimage,
including 0 and 1, and therefore proves the adopted positive-preimage reading.

## ASSUMED-UNVERIFIED

The OEIS text and attribution were independently retrieved on 2026-09-13.
The absence finding is bounded to the search surfaces listed above and does
not establish exhaustive literature coverage or first-publication priority.
The two numerical sieves and their counts were supplied by the orchestrator
and probe; this Stage-B seat did not rerun them. Source-to-Lean identification
is not itself a kernel-checked fact.
