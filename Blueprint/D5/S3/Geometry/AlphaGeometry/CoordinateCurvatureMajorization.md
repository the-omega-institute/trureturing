# CoordinateCurvatureMajorization

## Abstract

Strict positive T-transform chains for spectral cube-root curvature.

**Theorem 1.1 (spectral_moreMixed_monotone).**

$$\forall \{ n : \mathbb{N} \} (p q : \operatorname{Fin} n \to \mathbb{R}) , (2 \leq n) \to (p \in \operatorname{simplex} n) \to (q \in \operatorname{simplex} n) \to (\operatorname{moreMixed} q p) \to \operatorname{lambdaRatio} p \leq \operatorname{lambdaRatio} q$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.2 (spectral_moreMixed_strict).**

$$\forall \{ n : \mathbb{N} \} (p q : \operatorname{Fin} n \to \mathbb{R}) , (2 \leq n) \to (p \in \operatorname{simplex} n) \to (q \in \operatorname{simplex} n) \to (\operatorname{moreMixed} q p) \to (\neg \exists \pi : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} n) , q = p \circ \pi) \to \operatorname{lambdaRatio} p < \operatorname{lambdaRatio} q$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive T-transform chain contains a strict step unless its endpoints differ by a permutation. Monotonicity before and after that step gives strict spectral curvature comparison.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_monotone`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_strict`
- Dependency: [D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity](CubeRootSpectralMonotonicity.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone](LogScalarCurvatureMonotone.md)
