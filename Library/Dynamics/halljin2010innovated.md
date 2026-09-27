---
bibkey: "halljin2010innovated"
authors: "Peter Hall; Jiashun Jin"
year: 2010
title: "Innovated higher criticism for detecting sparse signals in correlated noise"
doi: "10.1214/09-AOS764"
url: "https://arxiv.org/abs/0902.3837v2"
claim: "Theorem 2.1 gives adaptive full power above the sparse Gaussian detection boundary for an exactly specified but growing support size, with locations sampled uniformly without replacement."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Innovated higher criticism for detecting sparse signals in correlated noise

The Annals of Statistics 38(3), 1686–1732 (2010), DOI 10.1214/09-AOS764.
The inspected source is the 49-page arXiv:0902.3837v2 PDF, revised
4 October 2010. Its first page gives the journal pagination and DOI;
Crossref corroborates the title, authors, year, journal, volume and issue.

Equation (2.2), PDF page 3, sets the exact number of nonzero coordinates
to `m = n^(1-beta)`, with fixed `1/2 < beta < 1`. Thus the cardinality is
deterministic at each dimension and grows to infinity. Equation (2.3),
page 4, draws the support uniformly without replacement. The principal
model gives all nonzero coordinates a common Gaussian mean magnitude.
The discussion following (2.4) also allows independent random nonnegative
strength multipliers; it retains the growing support count.

Theorem 2.1, PDF page 6, treats independent Gaussian noise. Higher
Criticism has asymptotically full power for every fixed `(beta,r)` strictly
inside `r > rho_*(beta)`, using a rule that knows neither parameter.
The surrounding argument also gives vanishing type I error. The paper
then treats correlated noise; its later covariance-dependent boundaries
must not be silently identified with the independent-noise curve.

Exact cardinality without replacement and adaptation to unknown sparsity
and strength are therefore `literature-attested`. This result does not
treat a constant positive integer count, deterministic heterogeneous
coordinatewise critical parameters, or their finite product-risk limit.
The compensated parity-kernel likelihood comparison and stationary-path
covariances require the separate `repo-derived` argument. No worldwide
originality claim follows from these scope differences.
