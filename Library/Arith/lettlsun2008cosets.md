---
bibkey: lettlsun2008cosets
authors: "Günter Lettl; Zhi-Wei Sun"
year: 2008
title: "On covers of abelian groups by cosets"
doi: 10.48550/arXiv.math/0411144
url: https://arxiv.org/abs/math/0411144
claim: "An essential class in a finite cover imposes lower bounds on the number of classes and on weighted prime-specific mismatches at a private point."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Essential classes and weighted prime mismatches

Published in *Acta Arithmetica* 131 (2008), no. 4, pages 341–350.
The inspected [arXiv v2](https://arxiv.org/pdf/math/0411144v2) is dated
11 March 2008; the first preprint was posted 7 November 2004. The full
statements and proofs below were checked 16 September 2026.

Theorem 1.3 states that an essential class of index n in an m-cover by k
cosets of an abelian group satisfies `k >= m + f(n)`, where
`f(n) = sum_p v_p(n)(p-1)`. For an inclusion-minimal ordinary cover of
the integers this applies to every original modulus. The paper attributes
the integer, m=1 case to Znám (1975); it is not a new covering-system bound.

Theorem 2.1 gives more information. At an integer a covered exactly m
times, let N_a be the least common multiple of the moduli covering a.
Let I(p) contain precisely those other original labels s for which the
prime-to-p part of n_s divides a_s-a, but n_s itself does not. Then
`sum_(s in I(p)) p^(-(v_p(n_s)-v_p(a_s-a)-1)) >= v_p(N_a)(p-1)`.
In the ordinary-cover case, a private point of class t has `N_a=n_t`.

These are necessary conditions for an actual cover. Irredundancy of a
noncovering family does not supply their coverage premise, and an isolated
smooth head of a full covering system need not satisfy them. The
[Erdős #7 dossier](../../Problems/erdos-7-odd-covering-systems.md) uses these
results to retain original labels when studying head and tail coordinates.
No Lean implementation of these public theorems is supplied by this note.

Citation and source-boundary note only; no source text or code is vendored.
