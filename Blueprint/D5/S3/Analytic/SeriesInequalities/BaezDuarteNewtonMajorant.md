# Baez-Duarte Newton Compact Majorant

## Abstract

Every-positive-epsilon decay of the actual coefficients yields a summable norm majorant on each compact subset of the open critical half-plane.

**Theorem 1.1 (An all-index majorant for the actual Newton terms).**

$$(\forall e \in \mathbb{R},\; 0<e\Rightarrow (\exists C \in \mathbb{R},\; 0<C\land (\exists N \in \mathbb{N},\; 1\le N\land (\forall k \in \mathbb{N},\; N\le k\Rightarrow \left|c\left(k\right)\right|\le C k^{-\frac{3}{4}+e}))))\Rightarrow (\forall K \in Set\left(\mathbb{C}\right),\; IsCompact\left(K\right)\land (\forall s \in \mathbb{C},\; s\in K\Rightarrow \frac{1}{2}<Re\left(s\right))\Rightarrow (\exists g \in \mathbb{N} \to \mathbb{R},\; Summable\left(g\right)\land (\forall k \in \mathbb{N},\; 0\le g\left(k\right))\land (\forall k \in \mathbb{N},\; (\forall s \in \mathbb{C},\; s\in K\Rightarrow \left\lVert c\left(k\right) P\left(k, \frac{s}{2}\right) \right\rVert\le g\left(k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant.baez_duarte_newton_compact_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

In the formula c denotes the imported actual baezDuarte sequence and P denotes normalizedPochhammer. The hypothesis is every-positive-epsilon eventual decay of the actual real baezDuarte coefficients, with a positive real constant and a natural threshold at least one. The conclusion supplies a nonnegative summable real sequence bounding every complex term c(k) P(k,s/2), for every index and every point of the compact set.

Compact separation gives a real lower bound a greater than one half. Choosing delta as (a minus one half) divided by four yields the common eventual exponent minus one minus delta. The producer's exact disk bound supplies the tail estimate. A finite-support correction from compact continuity bounds covers the whole prefix, including index zero. Compact separation and boundedness also apply to the empty compact set.

This is a repo-derived refinement of the source's compact convergence argument. The source proposition additionally identifies reciprocal zeta, which is not asserted here. The every-epsilon premise is retained as a hypothesis; neither RH direction is claimed. No nonpole, nonvanishing or real-only restriction is added. Utility kind none records a general analytic construction, not a finite computation.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant.baez_duarte_newton_compact_majorant`
- Dependency: [D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds](NormalizedPochhammerBounds.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RieszBaezDuarte](../../Weil/ZetaBridge/RieszBaezDuarte.md)
