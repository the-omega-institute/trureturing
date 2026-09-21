---
bibkey: abel2013binomial
authors: Ulrich Abel, Wolfgang Gawronski, and Thorsten Neuschel
year: 2013
title: Binomial Polynomials
doi: 10.1007/s40315-013-0013-3
url: https://doras.dcu.ie/31197/1/Binomialpolynomials.pdf
claim: Theorem 3.1 with r=l-1 and z=a^l gives the complete weighted binomial power-sum asymptotic for fixed a>0 and integer l>=2; this is a denominator estimate, not a truncated-ratio maximum theorem.
strata_touched:
  - D5/S3/AnalyticClosure/BinomialPowerNormalization
  - D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Analytic/abel2013binomial -->
# Complete weighted binomial power sums

Theorem 3.1 and its proof apply with the paper's parameter r=l-1>=1 and
z=a^l>0. For fixed a>0 and integer l>=2 they give

\[
D_n:=\sum_{i=0}^{n}(\binom ni a^i)^l
\sim\frac{(1+a)^{ln+l-1}}
              {(2\pi n a)^{(l-1)/2}\sqrt l}.
\]

For l=1, D_n=(1+a)^n exactly by the binomial theorem; the displayed
expression then agrees with that identity.

Put p=a/(1+a). For 0<=i<=n,
binomialMass(p,n,i)=choose(n,i) a^i/(1+a)^n. Dividing the complete weighted
sum by (1+a)^(ln) gives the equivalent probability normalization

\[
\sum_{i=0}^{n}\operatorname{binomialMass}(p,n,i)^l
\sim\frac{(2\pi n p(1-p))^{(1-l)/2}}{\sqrt l}.
\]

Conversely a=p/(1-p)>0 recovers every 0<p<1. Thus the arbitrary positive
weight in the repository normalization is a classical result. Its use
at a growing row r requires r to tend to infinity; application along
maximizing sequences additionally uses their positive limiting slope.

This source evaluates a complete row. It does not by this estimate alone
locate a maximizing truncation index or evaluate the maximum of a ratio
whose numerator is truncated in a different row. Those are distinct
obligations of Conjecture 1.1(d).

## Verified locator

- DOI: 10.1007/s40315-013-0013-3
- https://doras.dcu.ie/31197/1/Binomialpolynomials.pdf,
  Theorem 3.1 and its proof.

The bounded audit supplied with #9357 read all 18 pages, including the
theorem and proof. Crossref bibliographic metadata was consulted on
2026-09-21 UTC for author, title and 2013 publication identity. No new
discovery is claimed for this denominator asymptotic.

D5/L/Analytic/luca2012some records a different, unweighted complete-sum
supplier. Its restatement of McIntosh is not the evidence for arbitrary
positive a. The original McIntosh 1996 body (DOI 10.1006/jnth.1996.0072)
and the Binomial mean body (DOI 10.1080/02331888.2026.2631025) were not
inspected in that audit; no stronger exclusion claim is made about them.
