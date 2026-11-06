# Efron–Stein inequality on finite probability products

## Abstract

The variance of a bounded measurable observable on a finite dependent product is bounded by half its total coordinate resampling energy.

**Theorem 1.1 (Finite-product variance tensorization).**

$$\begin{aligned}\forall I: \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Omega: I \to \operatorname{Type}\left(\right), [\forall i: I, \operatorname{MeasurableSpace}\left(Omega\left(i\right)\right)] \\\forall mu: \forall i: I, \operatorname{Measure}\left(Omega\left(i\right)\right), [\forall i: I, \operatorname{IsProbabilityMeasure}\left(mu\left(i\right)\right)] \forall F: (\forall i: I, Omega\left(i\right)) \to \mathbb{R}, \operatorname{Measurable}\left(F\right) \Rightarrow\\\forall M: \mathbb{R}, (\forall x: (\forall i: I, Omega\left(i\right)), \left|F\left(x\right)\right| \leq M) \Rightarrow\\\operatorname{Var}\left(F, \operatorname{MeasurePi}\left(mu\right)\right) \le \frac{1}{2} \cdot \sum_{i: I} \int_{x} \int_{y} (F\left(\operatorname{update}\left(x, i, y\right)\right) - F\left(x\right))^{2} \operatorname{d}\left(mu\left(i\right)\right)(y) \operatorname{d}\left(\operatorname{MeasurePi}\left(mu\right)\right)(x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/EfronStein.efronStein_pi` (`✓ std3`). ∎

*Citation.* Scott N. Armstrong (2026). *CoarseGraining Efron-Stein source proof*. URL: <https://github.com/scottnarmstrong/CoarseGraining/tree/310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be/Homogenization/Probability/EfronStein>.

*Commentary.*

The index type is any finite type, including the empty type. Each coordinate has its own arbitrary measurable space and probability measure. The observable is a measurable real function on their dependent product with a single pointwise absolute bound M. The outer sample x follows the full product law, and the replacement y follows the probability measure of coordinate i. The coefficient is one half.

Splitting off one coordinate gives the two-factor variance decomposition. The two-point variance identity supplies that coordinate’s resampling term; Jensen’s inequality bounds each resampling term of the conditional mean by the corresponding term of the original observable. Induction on the number of coordinates and a measure-preserving reindexing give the stated finite-product inequality. The empty product has zero variance and an empty energy sum.

This is a credited port of Scott N. Armstrong’s CoarseGraining sources TwoPoint.lean, ProdDecomp.lean and Fin.lean at revision 310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be. The original Apache-2.0 copyright and full license are retained, with source correspondence in the literature note. The source proof is consolidated and adapted to the receiving Mathlib API.

Coordinates may differ and their measures need not be identical. No topology, Borel-space condition, symmetry or nondegeneracy is required. The conclusion concerns bounded observables and finite products; it supplies variance control from coordinate sensitivities.

## References

- Truth anchor: `D5/S3/Analytic/Probability/EfronStein.efronStein_pi`
