---
bibkey: bouthatchavezsheng2026graphinequalities
authors: Ludovick Bouthat, Ángel Chávez and Sam Sheng
year: 2026
title: A general framework for inequalities on simple graphs
doi: 10.48550/arXiv.2606.17356
url: https://arxiv.org/abs/2606.17356v1
claim: "Remark 4.3 proposes trigonometric and bilateral binomial expressions for the path CHS values, followed by a one-term simplification."
strata_touched:
  - D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43
  - D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation
license: citation-only
triage: anchor
---

# Path values in Remark 4.3

## Verified locator

DOI: 10.48550/arXiv.2606.17356

Source: https://arxiv.org/abs/2606.17356v1

Section 4.1, before Proposition 4.1: “The CHS norms of K_n, K_{r,s} and M_n have simple expressions. We leave the evaluation of ‖P_n‖_{X,d} as an open problem (see Remark 4.3).”

Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2:
‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].
The second expression reduces to a finite sum since almost all of the summands vanish. Indeed, the bounds can be replaced by −⌊(d−2)/(2(n+1))⌋ and 1 + ⌊d/(2(n+1))⌋. In particular, if n+1 ≥ d/2, the sum becomes ‖P_n‖_{X,d}^d = ((n² + n − d)/((n + d)(n + d + 1))) binom(n+d+1, d/2).”

The two identities and the final simplification are distinct statements. Integer-indexed sums use finsum, with zero binomial coefficients outside their natural range. The final simplification fails at n=2,d=6: the symmetric value is one and the expression is zero.

Literature completeness is ASSUMED-UNVERIFIED.
