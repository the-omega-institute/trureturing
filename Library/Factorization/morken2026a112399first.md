---
bibkey: morken2026a112399first
authors: Jamie Morken
year: 2026
title: First divisor-sum conjecture in OEIS A112399
doi: null
url: https://oeis.org/A112399/internal
claim: "For every n>=1, sum_{1<=k<=n,gcd(k,n)=1} mu(k) = sum_{d|n,mu(d)!=0} sum_{1<=m<=n/d,gcd(m,d)=1} mu(m)."
strata_touched:
  - D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum
license: citation-only
triage: anchor
---

# Morken's first A112399 conjecture

The FORMULA section of OEIS A112399, revision 41, timestamp
2026-09-19T09:22:12-04:00, attributes two conjectures to Jamie Morken on
September 18, 2026. The first is the double sum stated above. The entry's
NAME defines its left side using the signed integer Moebius function.
All indices are positive, upper endpoints are inclusive, and d ranges over
positive divisors, so n/d is exact. No squarefree restriction is placed on n.
The conjecture has AI-assisted provenance, which is independent of its
mathematical proof. The second conjecture and the
A372706 product-parameter identity are outside this result.

The proof combines standard Moebius multiplicativity and squarefree vanishing,
a multiplication reindexing, and Moebius cancellation over divisors of a gcd.
These standard facts are reused from the pinned Mathlib, rather than presented
as new arithmetic results. The exact first equality remains labelled a
conjecture in this source version. The bounded literature and ownership
screen is stated in research unit #25890; it is not an exhaustive claim that
no published proof exists.

## Verified locator

- URL: https://oeis.org/A112399/internal
- Location: A112399, revision 41, FORMULA, first equality following
  "Conjectures from Jamie Morken, Sep 18 2026"; NAME gives the coprime sum.
- Official exact-ID JSON: `https://oeis.org/search?q=id:A112399&fmt=json`,
  revision 41 and timestamp 2026-09-19T09:22:12-04:00.
