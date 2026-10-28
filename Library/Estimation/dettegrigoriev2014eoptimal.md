---
bibkey: dettegrigoriev2014eoptimal
authors: Holger Dette; Yuri Grigoriev
year: 2014
title: E-optimal designs for second order response surface models
doi: 10.1214/14-AOS1241
url: https://arxiv.org/abs/1403.3805v1
claim: E-optimality admits a positive semidefinite trace-one certificate supported on the minimum eigenspace, with equal sensitivity at supported design points.
strata_touched: []
license: citation-only
triage: anchor
---

# Minimum-eigenvalue design certificates

The primary source is [arXiv:1403.3805v1](https://arxiv.org/pdf/1403.3805v1),
Theorem 2.1, equation (2.5), and Remark 2.1, equation (2.6).
This note cites the source without redistributing its text or PDF.

For the paper's regression information matrix, Theorem 2.1 characterizes
optimality using orthonormal minimum-eigenvalue eigenvectors and
nonnegative weights summing to one. Their weighted outer products form
a positive semidefinite trace-one matrix. Its sensitivity is bounded
above by the optimal minimum eigenvalue and attains equality at
supported design points. Remark 2.1 gives the corresponding minimax
dual over these trace-one matrices.

In the FIB legal-edge-load volume's recorded-site experiment, each
site supplies one positive semidefinite matrix on the fixed
nonconstant phase space. An endpoint matrix includes two disjoint
readout blocks with one shared sampling weight. The direct Rayleigh
certificate used there is the same spectral mechanism applied to
these grouped matrices; the paper's scalar regression design points
are not independently assigned to the individual endpoint blocks.

The general certificate mechanism is literature-attested. It does
not establish the FIB activity-specific orthonormal reduction,
quartic root, strict spectral ordering or uniqueness against
nonsymmetric site weights. Those require the separate derivation.
Nor does E-optimality generally imply a rank-one certificate:
the source explicitly allows multiple minimum eigenvectors.

## Verified locator

- DOI: https://doi.org/10.1214/14-AOS1241
- Source: https://arxiv.org/abs/1403.3805v1
