---
bibkey: jianglimyaoye2011hodge
authors: Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye
year: 2011
title: Statistical ranking and combinatorial Hodge theory
doi: 10.1007/s10107-010-0419-x
url: https://arxiv.org/abs/0811.1067
claim: "Positive edge weights specify the cochain inner product and its adjoint; Hodge decomposition splits gradients from cyclic residuals orthogonally."
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted graph cochains and currents

The [primary preprint, arXiv:0811.1067v2](https://arxiv.org/pdf/0811.1067v2),
Definitions 4.2–4.3 and Lemma 4.4, pp. 16–18, specifies coboundaries,
weight-dependent adjoints and the identity of two consecutive coboundaries
with zero. Its divergence convention is minus the gradient adjoint.
Theorems 4.7–4.8, pp. 18–20, supply the orthogonal decomposition;
Theorem 5.1, pp. 21–22, applies the weighted normal equations to ranking.
The inner product in equation (14) uses positive weights on the edges
actually retained; zero weights denote absent edges.

For incidence columns equal to head minus tail, the consumer uses
$\delta_0=B^{\mathsf T}$. With vertex inner product matrix $M$ and edge
inner product matrix $W$, the adjoint is $M^{-1}BW$.
Transport from a cochain $a$ to a current $j=Wa$ changes the edge metric
to $W^{-1}$; cyclic currents satisfy $Bj=0$, whereas cyclic cochains
satisfy $BWa=0$. For a one-dimensional graph with no two-cells,
the coexact summand vanishes. A separately prescribed source potential
equals the gradient projection only when their boundaries match.

These are classical intermediate inputs to the
[five-edge weighted seam lift and clock obstruction](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md),
Section 15. The paper's ranking residual is not an independently supplied
observer error, probability flux, clock cost or physical force.
