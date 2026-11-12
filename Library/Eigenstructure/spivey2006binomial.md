---
bibkey: spivey2006binomial
authors: Michael Z. Spivey and Laura L. Steil
year: 2006
title: "The k-Binomial Transforms and the Hankel Transform"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL9/Spivey/spivey7.html
claim: "The falling weighted-binomial transform preserves every finite Hankel determinant."
strata_touched:
  - D5/S3/Combinatorics/Hankel/SunA006077
license: citation-only
triage: anchor
---

# The k-Binomial Transforms and the Hankel Transform

Section 3 defines the falling transform for nonzero k by
\(f_n=\sum_{i=0}^n\binom ni k^{n-i}a_i\).
At k=0 the source defines the transform as the original sequence;
the finite-sum formula has exactly the same value.
Section 6, Theorem 6.1 (physical pages 15–16 of the linked PDF), proves
\(H(F(A,k))=H(A)\), including integer \(k\) and arbitrary sequences.
This is exactly `translate_hankel_det` for integer sequences and parameter
`x=k`. Their order-n matrix has size n+1; the formal statement uses size N.
The missing size N=0 is the empty determinant convention, equal to one on
both sides. This attestation concerns weighted-binomial invariance, not
the complete Sun conjecture.

## Verified locator

URL: https://cs.uwaterloo.ca/journals/JIS/VOL9/Spivey/spivey7.html

Primary PDF: https://cs.uwaterloo.ca/journals/JIS/VOL9/Spivey/spivey7.pdf
