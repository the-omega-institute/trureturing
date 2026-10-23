# CubeRootSpectralMonotonicity

## Abstract

Moment-deficit positivity and strict spectral cube-root T-transform growth.

**Definition 1.1 (spectralN).**

$$\forall \{ n : \mathbb{N} \} (r : \operatorname{Fin} n \to \mathbb{R}) , \operatorname{spectralN} r = ((4 * (n : \mathbb{R}) ^{2} - 2) * (P n r 1) ^{2} - 2 * (n : \mathbb{R}) * P n r 2) * P n r 4 - 8 * (n : \mathbb{R}) * P n r 1 * P n r 5 + 8 * P n r 6$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of spectralN.

**Definition 1.2 (spectralRatio).**

$$\forall \{ n : \mathbb{N} \} (r : \operatorname{Fin} n \to \mathbb{R}) , \operatorname{spectralRatio} r = \operatorname{spectralN} r / (9 * (P n r 4) ^{2})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of spectralRatio.

**Definition 1.3 (lambdaRatio).**

$$\forall \{ n : \mathbb{N} \} (l : \operatorname{Fin} n \to \mathbb{R}) , \operatorname{lambdaRatio} l = \operatorname{spectralRatio} (\operatorname{fun} i \mapsto l i ^{(1 / 3 : \mathbb{R})})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of lambdaRatio.

**Theorem 1.4 (lambdaRatio_perm).**

$$\forall \{ n : \mathbb{N} \} (l : \operatorname{Fin} n \to \mathbb{R}) (p : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} n)) , \operatorname{lambdaRatio} (l \circ p) = \operatorname{lambdaRatio} l$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.5 (strict_t_transform_any_pair).**

$$\forall (n : \mathbb{N}) (l : \operatorname{Fin} n \to \mathbb{R}) (i j : \operatorname{Fin} n) (t : \mathbb{R}) , (2 \leq n) \to (\forall k , 0 < l k) \to (l j < l i) \to (0 < t) \to (t < 1) \to \operatorname{lambdaRatio} l < \operatorname{lambdaRatio} (((1 - t) \cdot l + t \cdot (l \circ \operatorname{Equiv} . \operatorname{swap} i j)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.strict_t_transform_any_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A strict equalizing T-transform increases the spectral curvature ratio. The derivative is positive before the midpoint; permutation symmetry handles the other half.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio_perm`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralN`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralRatio`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.strict_t_transform_any_pair`
- Dependency: [D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality](PairCurvatureInequality.md)
