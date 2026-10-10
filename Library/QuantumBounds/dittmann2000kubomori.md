---
bibkey: dittmann2000kubomori
authors: J. Dittmann
year: 2000
title: "On the curvature of monotone metrics and a conjecture concerning the Kubo–Mori metric"
doi: 10.1016/S0024-3795(00)00130-0
url: https://arxiv.org/abs/quant-ph/9906009v1
claim: "Theorem 2 gives the scalar curvature of the Kubo–Mori metric on faithful density matrices as an explicit spectral sum; Theorem 3 derives Petz's monotonicity conjecture from the concavity Assertion, through Lemma 4's four inequalities."
strata_touched:
  - D5/S3/Quantum/Petz/DittmannLemmaFourComplete
  - D5/S3/Quantum/Petz/SpectralPetz
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/S0024-3795(00)00130-0

Source: https://arxiv.org/abs/quant-ph/9906009v1

Journal DOI: 10.1016/S0024-3795(00)00130-0

# Dittmann, Kubo–Mori curvature and mixing

J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning
the Kubo–Mori metric*, Linear Algebra Appl. 315 (2000), 83–112;
arXiv:quant-ph/9906009v1.

## Source statement

Section 5, the Kubo–Mori example, culminates in Theorem 2: the scalar curvature
on faithful trace-one density matrices is the ordered spectral triple sum of
$d$, minus its diagonal sum, plus $(n^2-1)(n^2-2)/4$.
Section 6, “Monotonicity of $\mathcal S^1$ under mixing for the Kubo-Mori
metric”, states Petz's conjecture, the joint-concavity Assertion for the
symmetric kernel $h_s$, Lemma 4's four derivative inequalities (62)–(65),
and Theorem 3's implication from that Assertion to mixing monotonicity.

## Encoding and scope

`DittmannLemmaFourComplete.lemma4` uses the first partial derivative of the
smooth symmetric kernel and preserves all four positive-node quantifier lists.
The strict inequalities are proved without assuming joint concavity.
`SpectralPetz` is the interface for the resulting finite spectral majorization
statement. Spectral sums count labelled eigenvalue positions with multiplicity.
The dimension-dependent constant cancels in comparisons at fixed dimension.

Theorem 3's displayed derivative identity requires $h_s'$ in both terms of
its final double sum; the source's last negative term omits the prime.
Identification of the spectral expression with Riemannian scalar curvature
is the literature premise in Theorem 2, rather than a formalized geometric
result. The full joint-concavity Assertion remains open here.
