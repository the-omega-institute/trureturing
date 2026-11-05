# Hausdorff density in each natural dimension

## Abstract

Conformal Hausdorff density in the hyperbolic upper half-space.

Coordinates is the positive-height subtype of WithLp 2 (Complex times Real), with its Euclidean L2 distance. Native is HyperbolicThreeSpace with distance 2 arsinh(D/(2 sqrt(hx hy))), where D is coordinate distance and hx and hy are the two positive heights. Both spaces carry their Borel measurable structures. The measurable equivalence coordinatesEquiv retains the underlying point.

For a natural number d, rawCoordinateMeasureDim(d) and rawNativeMeasureDim(d) denote unnormalized Hausdorff d-measure for these respective metrics. The measurable function heightDensityDim(d) takes x to ofReal(height(x)^(-d)), an extended nonnegative real. The ambient spaces remain three-dimensional as d varies; d is the Hausdorff exponent.

**Theorem 1.1 (Natural-dimensional conformal density).**

$$\forall d \in Nat,\; \operatorname{map}\left(\operatorname{rawNativeMeasureDim}\left(d\right), coordinatesEquiv\right) = \operatorname{withDensity}\left(\operatorname{rawCoordinateMeasureDim}\left(d\right), \operatorname{heightDensityDim}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicHausdorffDimension.raw_native_density_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dennis Sullivan (1979). *The density at infinity of a discrete group of hyperbolic motions*. DOI: [10.1007/BF02684773](https://doi.org/10.1007/BF02684773). URL: <https://www.numdam.org/item/PMIHES_1979__50__171_0/>.

*Commentary.*

The classical conformal scaling principle is described in Sullivan, Section 1, printed page 174: on a Borel subset of a compact manifold with finite positive Hausdorff mass, a continuous conformal change of length scale changes that mass with the Hausdorff exponent. The countable-partition argument below supplies the whole-half-space measure identity, including infinite masses, in the stated original metrics.

The equality holds as an equality of measures for every natural d, without an extra finiteness or sigma-finiteness assumption. Map means pushforward under coordinatesEquiv. WithDensity multiplies the coordinate Hausdorff measure by heightDensityDim(d) through the lower integral. Thus both zero and infinite masses are included.

On a Euclidean coordinate ball of radius r below the positive centre height h, the coordinate map and its inverse have Lipschitz constants h+2r and 1/(h-r). The Hausdorff image inequalities raise these constants to the natural exponent d. Combining them with the corresponding pointwise height bounds controls the weighted coordinate measure and the pushed native measure in both directions.

For 0<epsilon<1, choose radius epsilon*h at each centre. The common comparison factor is ((1+2epsilon)/(1-epsilon))^d. These open balls cover the half-space. A Lindelof countable subcover, disjointified into Borel pieces, allows the local inequalities to be summed on every Borel set using countable additivity of extended nonnegative measures. This step requires no finite mass for a ball.

Set epsilon(n)=1/(n+2). The comparison factors tend to one. Their products with each fixed extended nonnegative mass b tend to b, including b=infinity, because the limiting multiplier is nonzero. Closedness of the order relation squeezes the two measures to equality on every Borel set. For d=0 the height density and distortion factor are identically one.

For d=2 the theorem supplies the height^(-2) density relative to ambient Euclidean-coordinate Hausdorff two-measure. It does not replace this measure by three-dimensional volume, and ambient Hausdorff two-measure is not assumed sigma-finite. Mathlib's euclideanHausdorffMeasure d multiplies both metric Hausdorff measures by the same dimension-dependent scalar; measure pushforward and withDensity commute with this scalar. The resulting normalized identity is independent of the separate three-dimensional volume calibration.

An isometric plane chart, its original image and its coordinate Jacobian remain separate inputs to a surface-area change of variables. This ambient measure identity alone gives no triangle moment formula, Schlaefli variation or manifold gluing theorem.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicHausdorffDimension.raw_native_density_nat`
- Dependency: [D5/S3/Geometry/HyperbolicNormalizedDensity](HyperbolicNormalizedDensity.md)
- Dependency: [D5/S3/Geometry/HyperbolicTopology](HyperbolicTopology.md)
