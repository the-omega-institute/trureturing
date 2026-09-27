---
bibkey: cohen2025cyclic
authors: Joel E. Cohen
year: 2025
title: "Conjectures about Primes and Cyclic Numbers"
doi: 10.48550/arXiv.2508.08335
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf
claim: Section 2.5 states Conjectures 28 and 29 and lists thresholds for twin-prime and consecutive cousin-prime pairs between consecutive cubes.
strata_touched:
  - D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation
license: citation-only
triage: anchor
---

# Prime pairs between consecutive cubes

Section 2.5, printed pages 17--18, states:

> **Conjecture 28** (number of twin primes between consecutive cubes). For
> every n ∈ N, the number of pairs of twin primes between n³ and (n + 1)³ is
> never less than two. More generally, for every k ∈ N, there exists N(k) ∈
> N such that for all n ≥ N(k) there are at least k pairs of twin primes
> between n³ and (n + 1)³. Specifically, N(1) = N(2) = 1, N(3) = 3,
> N(4) = 5, N(5) = 8, N(6) = N(7) = N(8) = N(9) = 10, N(10) = 11,
> N(11) = 13, N(12) = N(13) = N(14) = N(15) = N(16) = 15, and
> N(17) = 20.

The same section defines the second kind of pair:

> Two consecutive primes p, p' are defined [56, p. 336] to be cousin primes
> if |p - p'| = 4 and defined to be sexy primes if |p - p'| = 6. By these
> definitions, 3 and 7 are not cousin primes and 11 and 17 are not sexy
> primes because they are not consecutive. Every other pair of primes p, p'
> with |p - p'| = 4 is consecutive, hence cousin.

It then states:

> **Conjecture 29** (number of cousin primes between consecutive cubes). For
> n ∈ N with n > 1, the number of pairs of cousin primes between n³ and
> (n + 1)³ is never less than two. More generally, for every k ∈ N, there
> exists N(k) ∈ N such that, for all n ≥ N(k), there are at least k pairs
> of cousin primes between n³ and (n + 1)³. Specifically, N(1) = N(2) = 2,
> N(3) = 8, N(4) = N(5) = N(6) = N(7) = 9, N(8) = N(9) = N(10) = 12.

The paper's n = 1 example counts (3,5) and (5,7) between 1 and 8. The
formal definitions therefore count a pair only when both members lie
strictly inside the open interval: n³ < p and p + d < (n+1)³. For n at least
one, replacing the strict upper inequality by a non-strict one gives the
same predicate because (n+1)³ is composite. Cousin pairs additionally require
p+1, p+2, and p+3 to be nonprime, expressing the paper's consecutive-prime
condition and excluding (3,7).

The paper lists T(11) = 9 and C(12) = 7 in its two 25-term count sequences.
Those values contradict the printed thresholds N(10) = 11 in Conjecture 28
and N(8) = N(9) = N(10) = 12 in Conjecture 29. This note attests the printed
statements and definitions; it does not assert an eventual threshold or a
corrected formula.

The journal article has no journal DOI. The DOI in the frontmatter identifies
the arXiv preprint through DataCite.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2508.08335
- URL: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf
- Scope: Section 2.5, printed pages 17--18, Conjectures 28 and 29 and the
  definition of cousin primes.
