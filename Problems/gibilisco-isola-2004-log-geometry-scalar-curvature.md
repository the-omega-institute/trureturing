---
slug: gibilisco-isola-2004-log-geometry-scalar-curvature
bibkey: gibiliscoisola2005scalarcurvature
doi: 10.1063/1.1834693
url: https://arxiv.org/abs/math-ph/0407007v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result
---

# Logarithmic scalar curvature is strictly Schur-increasing

## Problem

Gibilisco and Isola, *On the monotonicity of scalar curvature in classical and quantum information geometry*, arXiv:math-ph/0407007v2, Conjecture 4.1, printed page 11:

> Suppose $n>2$. For the function $\mathrm{Scal}_p(\cdot):\mathcal P^1_n\to\mathbb R$ one has the following properties: if $p\in(1,2)$ then $\mathrm{Scal}_p$ is strictly Schur-decreasing; if $p\in(2,+\infty]$ then $\mathrm{Scal}_p$ is strictly Schur-increasing.

This settlement proves the $p=\infty$ endpoint only. The positive simplex is $\mathcal P^1_n=\{x\in\mathbb R^n: x_i>0,\ \sum_i x_i=1\}$. The source says $x$ is more mixed than $y$ when the decreasingly sorted initial sums of $x$ are at most those of $y$, with equal total sums. Strict Schur increase means weak curvature increase for all such pairs and strict increase unless $x$ is a permutation of $y$.

Definitions 4.3–4.4 define the $\alpha$-geometry as the Euclidean pull-back under $A_p(x)=p x^{1/p}$ for finite nonzero $p$ and $A_\infty(x)=\log x$, and $\mathrm{Scal}_p$ as its scalar curvature. The literal logarithmic pull-back, Christoffel symbols, Ricci contraction and decreasing-sort majorization are the conventions of [#15145](https://github.com/the-omega-institute/trureturing/issues/15145).

## Motivation

The endpoint gives an intrinsic curvature quantity that increases under mixing for every positive normalized vector of dimension at least three. Its motivation declaration is `D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result`.

## Gap

The preregistration #15145 records the external named conjecture, its tier-1 research-line classification, source quotations and literature screen. The source states it without proof; the recorded Andai follow-up gives curvature formulas and a mixing reduction. The recorded survey and citation search supply no all-dimension endpoint settlement. This is a bounded literature reading, not an exhaustive priority claim.

## Route

The coordinate logarithmic metric is diagonal plus rank one. Its inverse is obtained through Mathlib's Woodbury matrix inverse identity. Coordinate differentiation and the Gauss–Ricci contraction give a rational power-sum formula. Newton identities rewrite it as

$$\mathrm{Scal}_\infty(x)=\frac{2(e_3(x)-4e_4(x))}{s_2(x)^2},\qquad s_k(x)=\sum_i x_i^k.$$

For a pair with sum $u$ and product $v$, the rational numerator has a positive comparison factor $K$. The theorem `PairCurvatureInequality.key_pos` supplies its positivity under the stated pair/rest guards. A strict equalizing T-transform increases the product and the curvature. The transplanted LeanPool transfer theorem decreases Hamming disagreement while preserving prefix domination; `PositiveSimplexGeometryAndMixing.positive_sorted_chain` iterates it within the positive simplex. Sorting and permutation invariance give the final weak inequality and strict inequality outside permutation orbits.

The transfer is retained from LeanPool revision `7498a16d2393e1f02245cb265d67ec4fb2587814`, with the Apache-2.0 license and NOTICE chain in `docs/reports/brooks-suppliers/daviskahan-LICENSE.txt` and `daviskahan-NOTICE.txt`. It is retired when the repository's pinned Mathlib provides an equivalent transfer lemma.

## Falsifier

A dimension $n\ge3$ and positive normalized vectors $x,y$ with $x$ more mixed than $y$ but lower logarithmic scalar curvature would contradict the weak conclusion. Equal curvature for such a pair outside a permutation orbit would contradict the strict conclusion.

## Evidence

`D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.result : claim` is the settling theorem. The claim quantifies every natural dimension $n\ge3$ and every pair of positive normalized vectors. It concludes $\mathrm{Scal}_\infty(y)\le\mathrm{Scal}_\infty(x)$ and strict inequality if $x$ is not a permutation of $y$. The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

All 24 new public theorems, including `result`, have unfinished four-slot escape audits under [#15483](https://github.com/the-omega-institute/trureturing/issues/15483). No incomplete Reg source is included, and no registration is claimed validated. The source note is [the Geometry Library note](../Library/Geometry/gibiliscoisola2005scalarcurvature.md).

## Triage

### What the settlement shows

| Target item | Status | Evidence kind and scope |
| --- | --- | --- |
| Logarithmic metric, curvature formula and strict mixing mechanism | proved | Kernel-checked `PositiveSimplexGeometryAndMixing.scalarCurvature_powerSums`, `PairCurvatureInequality.key_pos`, `MajorizationTransfer.FiniteVector.exists_isTTransform_of_not_forall_le`, `PositiveSimplexGeometryAndMixing.positive_sorted_chain` and `LogScalarCurvatureMonotone.result`; the metric rank-one identity, coordinate Gauss identity and one-step strict estimate are consumed private declarations in those modules. |
| Numerical and symbolic readings | computed | The pinned experiment below; exact curvature samples at $n=3,4,5$, $p=2$ controls at $n=3,4$, identities for one through four remaining coordinates, and 20,000 random transforms in dimensions three through eight. |
| Finite-$p$ clauses of Conjecture 4.1 | open | Literature reading in #15145; no finite-$p$ settling theorem is delivered. |
| Quantum Conjecture 4.2 | open | Literature reading in #15145; its quantum $p=3$ slice is separate research line [#15179](https://github.com/the-omega-institute/trureturing/issues/15179). |

The proved endpoint covers all strictly positive simplex points in every dimension $n\ge3$, with the strictness boundary given by permutations. The pair argument also permits nonnegative rest coordinates when at least one is positive, as stated by the consumed private one-step estimate; it is not a boundary extension of the source's logarithmic metric. The geometric power-sum formula holds on the entire positive chart domain. No sharp extremal value, finite-$p$ extension, quantum extension or consequence for other source results is asserted.

Experiment entry: [docs/reports/gibilisco-isola-2004-log-geometry-scalar-curvature/check.py](https://github.com/the-omega-institute/trureturing-experiments/tree/f066618452743728214751f7b664bec6f8ebb53c/docs/reports/gibilisco-isola-2004-log-geometry-scalar-curvature). Command: `python3 check.py`; exit 0; script SHA-256 `cc52e5898b0f337118f302c51c75ed3cf5fccb96e30bb6fb65fc36b3bed8e1e6`; final reading `bad= 0`. The exact logarithmic curvature samples are $150/361$, $202/225$ and $3712/2025$ at dimensions three, four and five. The $p=2$ controls match $(n-1)(n-2)/4$ at dimensions three and four. The identities hold for one through four remaining coordinates; there are zero strict-increase violations among the 20,000 random T-transforms tested at dimensions three through eight. These finite computations do not by themselves prove the uniform result.

## ASSUMED-UNVERIFIED

The source and literature checks attributed to the orchestrator in #15145 are supplied evidence. Exhaustive worldwide priority, unpublished work and the finite-$p$ and quantum extensions are not verified here. The escape audit remains unfinished under #15483; this boundary is separate from the kernel proof.
