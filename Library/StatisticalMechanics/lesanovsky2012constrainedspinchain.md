---
bibkey: lesanovsky2012constrainedspinchain
authors: Igor Lesanovsky
year: 2012
title: Liquid ground state, gap and excited states of a strongly correlated spin chain
doi: 10.1103/PhysRevLett.108.105301
url: https://arxiv.org/abs/1110.1815v1
claim: The constrained spin-chain local parent has an exact normalized parity-conjugate correspondence with the FIB activity-law toggle projection; the paper's spectral formulas retain their boundary and homogeneity assumptions.
strata_touched: []
license: citation-only
triage: anchor
---

# A constrained-spin parent and its boundary conditions

The primary source is Lesanovsky,
*Physical Review Letters* 108, 105301,
[DOI:10.1103/PhysRevLett.108.105301](https://doi.org/10.1103/PhysRevLett.108.105301),
[arXiv:1110.1815v1](https://arxiv.org/pdf/1110.1815v1),
equations (1)--(2) and the boundary-condition
discussion. This note does not redistribute the
source text or PDF.

Write $P_i=|0\rangle\langle0|$, $n_i=|1\rangle\langle1|$
and $z_i=\sqrt{\lambda_i}>0$. The local constrained
parent has the form

$$
h_i(z_i)=P_{i-1}(\sigma_x+z_iP_i+z_i^{-1}n_i)P_{i+1}.
$$

For the FIB normalized activity-law site projection
$K_i$ and occupation-parity matrix $S$,

$$
SK_iS=h_i(z_i)/(z_i+z_i^{-1}).
$$

This is an exact local-operator correspondence.
The source's homogeneous periodic spectral formulas
do not automatically apply to arbitrary activities,
arbitrary site weights and open-path endpoint
updates. Its unpinned open-boundary setting also
has conserved edge-spin sectors, whereas the FIB
endpoint sites are updated. No physical preparation,
hardware realization or transferred spectral-gap
formula follows from the local identity alone.
