---
bibkey: bryant1986boolean
authors: Randal E. Bryant
year: 1986
title: 'Graph-Based Algorithms for Boolean Function Manipulation'
doi: 10.1109/TC.1986.1676819
url: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
claim: Reduced ordered function graphs give canonical representations of Boolean functions for a fixed variable order; representation size can depend strongly on that order.
strata_touched:
  - D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts
license: citation-only
triage: anchor
---

# Ordered Boolean function graphs

Published in IEEE Transactions on Computers C-35(8), 677–691 (1986).
The author-hosted PDF reconstructs the original electronic submission and
includes footnotes explicitly marked “Update”; its pagination differs from
the journal pagination.

## Verified scope

Section 1.1 defines restrictions/cofactors after assigning an input and fixes
one common order of variables. Section 2 defines ordered function graphs,
their isomorphisms and reduction. Theorem 1 states existence and uniqueness up
to isomorphism of a reduced graph for each Boolean function, together with
the corresponding graph-size minimality. The introduction and examples
explain the dependence on variable order and the possible exponential size.

## Repository use and limits

Section 79 of the boundary-dynamics theory volume uses remaining responses
as finite messages after each prescribed set of coordinates has been read.
This is related to merging identical residual Boolean functions, but it
counts reachable message labels at every externally specified position.
It does not equate those layer counts with the total number of nodes in a
reduced graph, which may skip irrelevant variables.

The explicit violation of submodularity, the bottleneck layout recurrences,
and the joint task/overlap-port quotient in that section are proved there.
They are not attributed to Bryant's Theorem 1. No complexity classification
of variable-order optimization is imported from this source, and no new
Lean result is asserted by this citation.

## Source

- [Author-hosted updated manuscript](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf).
- [Journal DOI](https://doi.org/10.1109/TC.1986.1676819).

This note is an original citation-only summary. No article text or PDF is
copied into the repository.
