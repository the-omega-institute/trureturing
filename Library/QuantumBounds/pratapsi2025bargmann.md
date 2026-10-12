---
bibkey: pratapsi2025bargmann
authors: Sagar Silva Pratapsi, Joao Gouveia, Leonardo Novo, and Ernesto F. Galvao
year: 2025
title: An Elementary Characterization of Bargmann Invariants
doi: 10.1103/hsnv-wpt3
url: https://arxiv.org/abs/2506.17132v3
claim: A common tuple of unit records obeys a sharp phase-dependent arithmetic-mean overlap bound, supplied by circulant averaging and the regular polygon of Bargmann roots.
strata_touched: []
license: citation-only
triage: anchor
---

# Common-record polygon bound used by the five-label square

Primary text: [arXiv:2506.17132v3](https://arxiv.org/pdf/2506.17132v3),
Theorem 1 and Theorem 5, equations (20)–(27).
Published identifier: [10.1103/hsnv-wpt3](https://doi.org/10.1103/hsnv-wpt3).
The consumer is [Hidden Relations, C-29.3–C-29.5](../../docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#29-同一五模式的全输入保真方形记录与稳定子块):
the actual comparison graph has a square and a pendant edge.

For $m\ge3$ common unit vectors, let

$$
\Delta=\prod_{j=0}^{m-1}\langle e_j|e_{j+1}\rangle,
\qquad e_m=e_0,\qquad
v_j=|\langle e_j|e_{j+1}\rangle|.
$$

Assume all adjacent overlaps are nonzero and put
$\Theta=|\operatorname{Arg}\Delta|\in[0,\pi]$. The consumed bound is

$$
\min_jv_j\le\frac1m\sum_jv_j
\le\eta_m(\Theta)=\frac{\cos(\pi/m)}{\cos((\pi-\Theta)/m)},
\qquad |\Delta|\le\eta_m(\Theta)^m.
$$

The average bound comes from Theorem 5's proof, not from its product-range
corollary alone. Equations (20)–(21) align the edge phases on one ray;
equations (23)–(24) identify the mean modulus with the magnitude of the mean
overlap; equations (26)–(27) cyclically average the positive Gram matrix.
Theorem 1 places this circulant first-neighbor entry $z$ in the convex hull
of the $m$th roots of unity. After conjugating the orientation if necessary,
$z=\overline v e^{i\Theta/m}$. The supporting line

$$
\operatorname{Re}(e^{-i\pi/m}z)\le\cos(\pi/m)
$$

gives the displayed arithmetic-mean inequality. AM–GM then gives the
product bound. The intersection of the ray with this polygon edge is a
convex combination of its two endpoint roots. Theorem 1's circulant Gram
realization has rank at most two there and equal edge moduli, attaining
both bounds. This argument and construction are published results; they
are not a new general polygon theorem of the project.

For $m=4$ the denominator simplifies to
$\eta_4(\Theta)=1/(\cos(\Theta/4)+\sin(\Theta/4))$.
Equivalently, the averaged square Gram has first-neighbor entry
$z=\overline v e^{i\Theta/4}$ and a real opposite entry $t$; its eigenvalues
are $1+t\pm2\overline v\cos(\Theta/4)$ and
$1-t\pm2\overline v\sin(\Theta/4)$. Their nonnegativity gives the same bound.
At $\Theta=\pi$, the values for $m=3,4,5,6$ are respectively
$1/2,1/\sqrt2,(1+\sqrt5)/4,\sqrt3/2$; as $m\to\infty$ they tend to one.
The five-label native graph does not supply a five-cycle: a polygon with
another number of comparison edges requires its own common-record contract.

The paper uses the standard overlap orientation in $\Delta$. The repository
channel convention is $\Gamma_{st}=\langle e_t|e_s\rangle$, so the product
$B$ along the same directed cycle is $\overline\Delta$. Absolute principal
angles and all displayed bounds agree. Rephasing vectors is a mathematical
Gram transformation; performing a calibrated system correction requires an
additional physical operation. Pairwise overlaps from unrelated records
cannot replace the one positive Gram matrix used here. A zero edge makes
$\operatorname{Arg}\Delta$ undefined.

## Refinement comparison consumed by the recovery bound

The explicit real records
$e_j=(\cos(j\pi/m),\sin(j\pi/m))$, $0\le j<m$, have positive consecutive
inner products $\cos(\pi/m)$ except for the closing edge, which is
$-\cos(\pi/m)$. Thus

$$
\Delta=-\cos(\pi/m)^m\longrightarrow-1.
$$

Indeed $0\le1-\cos(\pi/m)^m\le m(1-\cos(\pi/m))\le\pi^2/(2m)$.
For even $m$, $e_0$ and $e_{m/2}$ are orthogonal. Consequently the consumer's
pair-state contraction bound still forces system-only recovery error at
least $1/2$, although adjacent moduli approach one. On the open chain the
root depth is $m-1$, and its local real-part defect is
$1-\cos(\pi/m)$; the product of depth and square root of that defect does
not approach zero. This comparison varies the number of labels and does
not assert a fixed-five-label limit or a global impossibility theorem.
