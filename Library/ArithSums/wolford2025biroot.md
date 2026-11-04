---
bibkey: wolford2025biroot
authors: Isaac Wolford
year: 2025
title: "Combinatorial and Gaussian Foundations of Rational Nth Root Approximations: Theorems and Conjectures"
doi: 10.48550/arXiv.2508.14095
url: https://arxiv.org/abs/2508.14095v3
claim: "Conjecture 3.4: the generalized binomial biroot converges for all positive real x,c and every positive integer n."
strata_touched:
  - D5/S3/ArithSums/WolfordBinomialBiroot
license: citation-only
triage: anchor
---

# Generalized binomial biroot

Wolford, arXiv:2508.14095v3, Conjecture 3.4 states:

> For any $x > 0$, positive integer $n$, and $c > 0$,
> $$\lim_{m \to \infty} \beta^n_m(x, c) = \sqrt[n]{x}$$
> where $\beta^n_m(x,c)$ is defined as above.

The definition in Section 3.1.3 is

$$
\beta^n_m(x,c)=
\frac{\sum_{k=0}^{\lceil m/n\rceil}x^k c^{m-nk}\binom m{nk}}
{\sum_{k=0}^{\lceil m/n\rceil-1}x^k c^{m-nk-1}\binom m{nk+1}}.
$$

Both bounds are inclusive. Powers of positive c have integer exponents.
The source explicitly sets binomial coefficients to zero when the lower
index exceeds the upper index. The positive-index denominator contains
its strictly positive k=0 term. Index m=0 is outside the positive-index
limit. The positive real nth root is x raised to the reciprocal real n.

## Locator

DOI: 10.48550/arXiv.2508.14095; URL: https://arxiv.org/abs/2508.14095v3.

## Primary source

The v3 source archive is https://arxiv.org/src/2508.14095v3.
Its SHA-256 is `4ad7f2346693d8cdb2c686f90416dd1a1d56229dace1c7ae84203209692d8a8a`.
The member `main.tex` has SHA-256
`3402df742475b710e44e388927ebd5f8fd81b8537a67c4dc55ef9a1f70a49156`.
The definition is at line 339, the conjecture at lines 357–361,
the statement that no general proof is attempted at line 363, and the
explicit zero-extension convention at line 448. The arXiv metadata
identifies v3 as the version of 2025-11-16; the first submission is from
2025-08-15. These are source version identifiers.

## Related source and scope

Shunia and Prunescu, *Short Recurrences and Straight-Line Programs for
Primes*, arXiv:2610.13365v1, Appendix A.3, proves its integer-root term
under integer radicand and root-index restrictions. Its coefficient
multisection and root-of-unity expression are related mathematics; its
stated result is not the arbitrary-positive-real Wolford assertion.
The archive SHA-256 is
`6a26773124ae8a9277b857c7fbb738857270bc37d7174a1b154502ad0852d496`;
its `main.tex` SHA-256 is
`f886d4a8c2469506f460576095973089e7d2df80908b1978310e49f3a0eb152b`.

The checked primary and nearby source contain no proof of the exact
full assertion. This bounded source comparison establishes neither
worldwide openness nor priority. Loogle and LeanSearch access is denied;
Reservoir catalog availability does not establish a filtered theorem
search. The proof uses the retained finite stochastic mixing supplier;
no third-party theorem or paper proof is copied into this module.

## Attribution

The quoted conjecture and definition are attributed to Isaac Wolford.
This note is bibliographic and citation-only; it grants no license to
redistribute the original paper or its figures. The Lean proof is a
separate repository derivation.
