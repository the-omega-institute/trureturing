---
bibkey: mbirikaspilker2023oddgcd
authors: aBa Mbirika, Jürgen Spilker
year: 2023
title: GCD of sums of k consecutive squares of generalized Fibonacci numbers
doi: null
url: https://arxiv.org/abs/2204.12626v2
claim: 'Question 6.4: Under what conditions on the initial values G_0 and G_1 are the linear and square block-sum gcd sequences periodic on odd k values?'
strata_touched:
  - D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity
license: citation-only
triage: anchor
---

# Gibonacci square-window gcds and the joint odd-length question

Question 6.4 in Section 6.2 asks verbatim:

> Under what conditions on the initial values G_0 and G_1 are
> G_{G_0,G_1}(k) and G^2_{G_0,G_1}(k) periodic on odd k values?

Here the two symbols denote the gcds, over **every natural shift** t, of
the actual sums `sum(i=1..k) G(t+i)` and `sum(i=1..k) G(t+i)^2`.
Definition 2.1 permits arbitrary integer initial values and specifies
`G(n+2)=G(n)+G(n+1)`. Convention 2.2 and Convention 3.7 reduce the discussion
to relatively prime seeds through scaling; Theorem 3.6 gives square scaling.
Example 6.3 states equality at k+6 and k+30 for all odd k, so the target is
periodicity from the first odd length. It asks for no minimal period.

Theorem 3.4 proves the finite square-gcd formula, and Theorem 4.8 proves
that its odd-length values divide `|2mu|`, where `mu=b^2-ab-a^2`.
These are prior results. Guyer-Mbirika, arXiv:2104.12262v2, Theorems 3.1
and 3.5, gives the linear finite-gcd and scaling formulas. Chen-Pan,
*Greatest Common Divisors of Shifted Horadam Sequences*, JIS 23,
Article 20.5.8, gives the linear periodicity corollary and the modular-state
method. For that corollary the parameters are
`p=1, q=-1, s=-b, t=-(a+b), phi(j)=2j+2`; the fixed multiple is `-2mu`.

The Lean result includes every integer seed pair directly and proves the
universal divisor specifications of both infinite gcds. Its zero-seed
clause is the normalized extension `gcd(0,0,...)=0`, separate from the
source's primitive convention. Its common positive period is for the
odd subsequences starting at length one. The proof uses the known odd
cap and an existing complete modular-state return, rather than an
inference from boundedness alone.

The bounded comparison does not establish first-publication priority.
The supplied comparison of adjacent literature found no verified whole
two-family duplicate in its inspected results. Spilker's 2016 generalized
chapter was not available in full; equivalent whole coverage there remains
unverified. This does not convert an inaccessible source into evidence
of absence.

## Verified locator

- Version and bibliographic page: https://arxiv.org/abs/2204.12626v2
- Primary text: https://arxiv.org/html/2204.12626v2, Definition 2.1,
  Conventions 2.2 and 3.7, Theorems 3.4, 3.6 and 4.8, and Section 6.2.
- Linear formulas: https://arxiv.org/html/2104.12262v2,
  Theorems 3.1 and 3.5.
- Chen-Pan primary TeX:
  https://cs.uwaterloo.ca/journals/JIS/VOL23/Pan/pan32.tex,
  the theorem labeled `Thm:periodic` and its proof.
