---
bibkey: boldi2026sweep
authors: Paolo Boldi; Sebastiano Vigna
year: 2026
title: "The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension"
doi: 10.48550/arXiv.2610.41385
url: https://arxiv.org/abs/2610.41385v1
claim: "Section 6 asks which finite posets attain the lower sweep-dimension bound max(2,width) and the upper bound 2*width."
strata_touched:
  - D5/S3/Combinatorics/SweepDimension/Basic
  - D5/S3/Combinatorics/SweepDimension/Upper
  - D5/S3/Combinatorics/SweepDimension/Endpoints
license: citation-only
triage: anchor
---

# Sweep dimension and its endpoints

## Verified locator

https://doi.org/10.48550/arXiv.2610.41385

https://arxiv.org/abs/2610.41385v1

https://arxiv.org/html/2610.41385v1

Section 2 defines an interval as every order-convex subset, not only a principal
interval. Empty and full subsets are included. Definition 1 uses arbitrary
linear orders: for every interval I and every y outside I there is an order
placing y before every member of I. There is no linear-extension restriction.

Section 6, second closing bullet, asks to determine sweep dimension for trees,
products of chains and Boolean lattices, and to characterize the posets attaining
the lower bound max(2,width) or the upper bound twice the width. The inequalities
and the endpoint question have the at-least-two-points scope. The source does not
state the general theta identity as an existing theorem.

The associated general endpoint answer uses theta, the largest size of a subset
without a strict three-chain. The lower bound removes each selected point and
uses the convex hull of the others. The upper bound applies finite Dilworth to
the product with the two-element chain. These proof ingredients are classical;
no priority claim for them is made.

The product-of-chains and Boolean question belongs to issue 25960. Tree recurrences,
the lambda second term, and staircase-region questions are separate and are not
claimed by the general endpoint result.
