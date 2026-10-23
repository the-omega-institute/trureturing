---
bibkey: dyergreenhillullrich2014heatbath
authors: Martin Dyer; Catherine Greenhill; Mario Ullrich
year: 2014
title: Structure and eigenvalues of heat-bath Markov chains
doi: 10.1016/j.laa.2014.04.018
url: https://arxiv.org/abs/1301.4055v3
claim: A state-independent mixture of heat-bath conditional-resampling kernels has nonnegative transition spectrum; this does not compare its two nontrivial spectral edges.
strata_touched: []
license: citation-only
triage: anchor
---

# Nonnegative spectrum of heat-bath mixtures

The primary source is Dyer--Greenhill--Ullrich,
*Linear Algebra and its Applications* 454, 57--71,
[DOI:10.1016/j.laa.2014.04.018](https://doi.org/10.1016/j.laa.2014.04.018),
[arXiv:1301.4055v3](https://arxiv.org/pdf/1301.4055v3),
Definition 1.1 and Lemma 1.2. This note does not
redistribute the source text or PDF.

Each heat-bath update resamples within a conditional
class from the stationary law. It is idempotent and
reversible. The source proves that a state-independent
mixture of these updates has no negative eigenvalues.

For a finite positive legal-word law, the FIB site
update resamples each legal toggle pair and keeps
blocked singleton words fixed. With
$D=\operatorname{diag}(\sqrt p)$ and the symmetric
site-parent operator $H_\omega$, its transition
matrix is $T_\omega=I-D^{-1}H_\omega D$.
The cited result gives $0\preceq H_\omega\preceq I$
after symmetrization. It does not give the stronger
comparison $\gamma(H_\omega)+\Lambda(H_\omega)\le1$,
nor the associated Fisher-design optimization.

The transition operator is a classical conditional
update. Its diagonal symmetrization does not identify
that stochastic update with real-time unitary motion.
