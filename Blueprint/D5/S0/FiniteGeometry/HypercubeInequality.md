# The All-Dimensional Hypercube Inequality

## Abstract

The determinant-defined Hypercube Inequality holds in every positive dimension.

**Definition 1.1 (The augmented cube matrix).**

$$\begin{aligned}\forall d \in \mathbb{N}, \operatorname{A}\left(d\right): \left(\left(\operatorname{Fin}\left(d\right) + \{*\}\right) \times \{0,1\}^{d}\right) \to \mathbb{Z},\\\operatorname{A}\left(d, \operatorname{inl}\left(i\right), v\right) = v_{i}, \operatorname{A}\left(d, \operatorname{inr}\left(*\right), v\right) = 1.\end{aligned}$$

*Formalization.* `D5/S0/FiniteGeometry/HypercubeInequality.augmentedCube` (`✓ std3`).

*Citation.* Gennadiy Averkov; Katherina von Dichter; Ivan Soprunov (2026). *On the Log-submodularity for zonoids: from Mixed Volume inequalities to the Hypercube*. URL: <https://arxiv.org/html/2608.14909v1#S4.E16>.

*Commentary.*

The columns are indexed by Boolean cube vertices. The first d rows are the vertex coordinates, cast to integers, and the final row is one. Thus every maximal minor is the oriented normalized volume of its unordered (d+1)-vertex subset.

**Definition 1.2 (The weighted normalized-volume sum).**

$$\begin{aligned}\forall d \in \mathbb{N}, x: \{0,1\}^{d} \to \mathbb{R},\\\operatorname{W}\left(d, x\right) = \sum_{S \subseteq \{0,1\}^{d}, \operatorname{card}\left(S\right) = d + 1} \left|\operatorname{det}\left(\operatorname{columns}\left(\operatorname{A}\left(d\right), S\right)\right)\right| \prod_{v \in S} x_{v}.\end{aligned}$$

*Formalization.* `D5/S0/FiniteGeometry/HypercubeInequality.hypercubeWeight` (`✓ std3`).

*Citation.* Gennadiy Averkov; Katherina von Dichter; Ivan Soprunov (2026). *On the Log-submodularity for zonoids: from Mixed Volume inequalities to the Hypercube*. URL: <https://arxiv.org/html/2608.14909v1#S4.E16>.

*Commentary.*

The sum ranges once over every finite subset of cube vertices with cardinality d+1. Its coefficient is the absolute integer determinant of the actual augmented columns, multiplied by the weights on the subset. There is no ordering multiplicity and no factorial normalization.

**Theorem 1.3 (Equation (16) in every positive dimension).**

$$\begin{aligned}\forall d \in \mathbb{N}, 1 \leq d,\\\forall x: \{0,1\}^{d} \to \mathbb{R}, \left(\forall v \in \{0,1\}^{d}, 0 \leq x_{v}\right) \implies\\\operatorname{W}\left(d, x\right) \left(\sum_{v \in \{0,1\}^{d}} x_{v}\right)^{d - 1} \leq \prod_{i \in \operatorname{Fin}\left(d\right)} \left(\sum_{v \in \{0,1\}^{d}, v_{i} = 0} x_{v}\right) \left(\sum_{v \in \{0,1\}^{d}, v_{i} = 1} x_{v}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/HypercubeInequality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hypercube-inequality` (proved) by `D5/S0/FiniteGeometry/HypercubeInequality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hypercube-inequality","declaration_gid":"D5/S0/FiniteGeometry/HypercubeInequality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gennadiy Averkov; Katherina von Dichter; Ivan Soprunov (2026). *On the Log-submodularity for zonoids: from Mixed Volume inequalities to the Hypercube*. URL: <https://arxiv.org/html/2608.14909v1#S4.E16>.

*Commentary.*

For every d at least one and every nonnegative real weight on the Boolean cube, the determinant-weighted sum times the total weight to the power d-1 is bounded by the product of the two opposite facet sums in every coordinate.

The proof first expands the weighted Gram determinant by maximal minors using the characteristic-polynomial minor formula and det(1+PQ)=det(1+QP). Integer determinants satisfy |det| <= |det|^2, so the source weight is bounded by this positive semidefinite determinant.

If the total weight is zero, nonnegativity makes every weight and both sides zero. Otherwise the final scalar block is positive. Its Schur complement, scaled by the total weight, is positive semidefinite and has diagonal entries equal to the products of the two exact coordinate-facet sums. A Gram factorization and the orientation volume bound compare its determinant with the product of those diagonal entries. The Schur determinant identity supplies exactly the factor s^(d-1). Singular Gram matrices and zero facet sums require no division or positivity assumption beyond the separated total-zero case.

## References

- Truth anchor: `D5/S0/FiniteGeometry/HypercubeInequality.augmentedCube`
- Truth anchor: `D5/S0/FiniteGeometry/HypercubeInequality.hypercubeWeight`
- Truth anchor: `D5/S0/FiniteGeometry/HypercubeInequality.result`
