---
bibkey: "wolfer2021reversible"
authors: "Geoffrey Wolfer; Shun Watanabe"
year: 2021
title: "Information Geometry of Reversible Markov Chains"
doi: "10.1007/s41884-021-00061-7"
url: "https://doi.org/10.1007/s41884-021-00061-7"
claim: "The reverse-relative-entropy projection onto reversible Markov kernels is the Perron stochastic rescaling of the entrywise geometric mean of a kernel and its time reversal, when their common support is strongly connected."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Information Geometry of Reversible Markov Chains

Information Geometry 4, 393–433 (2021). Section 6, Theorem 7, on journal page
418 gives the e-projection and its Pythagorean identity; the proof continues
on pages 419–420. The stochastic rescaling is defined in equation (3).
For the e-projection, the intersection of the forward and reversed supports
must be strongly connected. Strictly positive finite kernels satisfy this
hypothesis. Time reversal is taken with respect to the kernel's stationary law.

This is `literature-attested` background for the reversible Perron tilt in the
parity-kernel testing proof. With uniform stationarity, the reversed kernel
is the transpose and the geometric-mean matrix is symmetric. The projection
construction is established literature; the rank-four factorization and the
quartic depending on two parity-block averages are `repo-derived`
specializations. The Bayes exponent proof separately controls its endpoint
factor and supplies a subexponential lower bound.
