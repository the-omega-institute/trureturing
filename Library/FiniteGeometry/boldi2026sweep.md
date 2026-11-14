---
bibkey: boldi2026sweep
authors: Paolo Boldi; Sebastiano Vigna
year: 2026
title: "The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension"
doi: 10.48550/arXiv.2610.41385
url: https://arxiv.org/abs/2610.41385v1
claim: "Section 2 and Definition 1 define intervals, sweep systems and sweep dimension; Section 4.3 Proposition 3 defines theta and proves theta <= sweepdim for at least two points; Section 6 asks for the width-bound endpoint classifications."
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
The orders form an indexed family and may repeat. Definition 1 also defines
sweep dimension as the minimum size of such a family.

Section 4.3, Proposition 3 defines theta as the maximum cardinality of a subposet
without a three-element chain. Item (3) proves theta(P) <= sweepdim(P), under the
proposition's hypothesis |P| >= 2. The proof of item (2) uses the order-convex hull
of a subset, consisting of points between two of its elements, to restrict sweep
systems. Item (3) then observes that distinct points in a three-chain-free
subposet require distinct sweeps.

The formalized lower bound theta_le_of_sweep expresses this published ingredient
for each k-order sweep system, without taking the minimum. Its proof also covers
empty and singleton carriers, extending the stated scope of Proposition 3;
these boundary cases are repository derivations, not claims of that proposition.

Section 6, second closing bullet, asks to determine sweep dimension for trees,
products of chains and Boolean lattices, and to characterize the posets attaining
the lower bound max(2,width) or the upper bound twice the width. The inequalities
and the endpoint question have the at-least-two-points scope. The source does not
state the general theta identity as an existing theorem.

The repository's general identity sweepDimension_eq_theta and full endpoint
classifications are separate derived results, not statements attributed to the
paper. Their lower-bound ingredient is Proposition 3(3) as identified above;
their upper construction applies finite Dilworth to the product with the
two-element chain. These proof ingredients are classical; no priority claim for
them is made.

The product-of-chains and Boolean question belongs to issue 25960. Tree recurrences,
the lambda second term, and staircase-region questions are separate and are not
claimed by the general endpoint result.
