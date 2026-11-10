---
bibkey: kaplan2007dottie
authors: Samuel R. Kaplan
year: 2007
title: The Dottie Number
doi: 10.1080/0025570X.2007.11953455
claim: Source of the name Dottie number for the unique real solution of cos x = x, approximately 0.739085, which is the unique real fixed point of the cosine and the limit of the cosine iteration from every real starting value.
strata_touched:
  - D5/S1/FixedPoints/SignedCosineFeedback
license: citation-only
triage: anchor
---

# The Dottie Number

## Verified locator

DOI: https://doi.org/10.1080/0025570X.2007.11953455

Mathematics Magazine 80 (2007), no. 1, pages 73-74. The Crossref record for this DOI gives the title "The Dottie Number", the author Samuel R. Kaplan, the journal Mathematics Magazine, volume 80, issue 1, pages 73-74, issued February 2007.

## Source statements

The article text was not read: the publisher page for the DOI refused access. The statements below are quoted from the MathWorld entry "Dottie Number" (https://mathworld.wolfram.com/DottieNumber.html), which cites the article as Kaplan, S. R. "The Dottie Number." Math. Mag. 80, 73-74, 2007.

> The Dottie number is the unique real root of cos x = x (namely, the unique real fixed point of the cosine function), which is 0.739085... (OEIS A003957; Kaplan 2007).

> Starting from any real x_0, the fixed point iteration x_(n+1) = cos x_n converges to the Dottie number.

> This root is a simple nontrivial example of a universal attracting fixed point.

The same entry states that the number itself is older than the name:

> The number is well-known, having appeared in numerous elementary works on algebra already by the late 1880s ...

That the wording of the article itself agrees with these sentences is ASSUMED-UNVERIFIED.

## Relation to the formal statements

`D5/S1/FixedPoints/SignedCosineFeedback.signed_cosine_feedback_fixed_point` proves existence of a solution r of cos r = r in the open unit interval, its uniqueness among all real numbers, and convergence of the cosine iteration from every real starting value. These are the three facts quoted above, with r the Dottie number.

The formal statement contains further clauses that the quoted sentences do not state: the contraction estimate with constant sin 1 on the closed interval from -1 to 1 and the resulting error bound after the first step, the same conclusions for the mirror map sending x to -cos x with fixed point -r, the absence of a common real solution of cos x = x and cos x = -x, the orbit of period two of the sign-alternating map on pairs, and the convergence of absolute values to r when the sign is chosen freely at every step.
