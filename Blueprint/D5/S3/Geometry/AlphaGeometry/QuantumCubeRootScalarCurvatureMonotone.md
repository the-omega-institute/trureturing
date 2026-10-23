# QuantumCubeRootScalarCurvatureMonotone

## Abstract

Quantum cube-root scalar curvature is strictly Schur-increasing.

**Definition 1.1 (densityStates).**

$$\forall (n : \mathbb{N}) , \operatorname{densityStates} n = \{ A : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \mid A . \operatorname{PosDef} \land A . \operatorname{trace} = 1 \}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.densityStates` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Definition 2.5 (printed p. 4) defines “D¹ₙ := {ρ ∈ Mⁿ | Trρ = 1, ρ > 0}”. The carrier is the space of complex n by n matrices; Matrix.PosDef supplies Hermitian symmetry and strict positivity.

**Definition 1.2 (metric).**

$$\forall \{ n : \mathbb{N} \} (x : \operatorname{Fin} (n ^{2} - 1) \to \mathbb{R}) , \operatorname{metric} x = \operatorname{fun} (i j : \operatorname{Fin} (n ^{2} - 1)) \mapsto \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((\operatorname{fderiv} \mathbb{R} (\operatorname{alphaEmbed3} \circ \operatorname{rho}) x (\operatorname{Pi} . \operatorname{single} i 1))) * ((\operatorname{fderiv} \mathbb{R} (\operatorname{alphaEmbed3} \circ \operatorname{rho}) x (\operatorname{Pi} . \operatorname{single} j 1)))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.metric` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The defining expression of metric.

**Definition 1.3 (scal3).**

$$\forall \{ n : \mathbb{N} \} (A : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , \operatorname{scal3} A = \operatorname{scalarCurvature} \operatorname{metric} (\operatorname{chartPoint} A)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.scal3` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Definition 4.6 (printed p. 11): “We denote by Scalₚ(ρ) the scalar curvature of the α-geometry (with p = 2/(1−α)) at the point ρ ∈ D¹ₙ.” The p = 3 curvature is the coordinate Christoffel–Ricci contraction of the pull-back metric.

**Definition 1.4 (eig).**

$$\forall \{ n : \mathbb{N} \} (A : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , \operatorname{eig} A = \operatorname{if} h : A . \operatorname{IsHermitian} \operatorname{then} h . \operatorname{eigenvalues} \operatorname{else} 0$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.eig` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of eig.

**Definition 1.5 (claim).**

$$\operatorname{claim} = \forall n : \mathbb{N} , 2 \leq n \to \forall A B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} , A \in \operatorname{densityStates} n \to B \in \operatorname{densityStates} n \to \operatorname{PositiveSimplexGeometryAndMixing} . \operatorname{moreMixed} (\operatorname{eig} A) (\operatorname{eig} B) \to \operatorname{scal3} B \leq \operatorname{scal3} A \land ((\neg \exists \operatorname{pi} : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} n) , \operatorname{eig} A = \operatorname{eig} B \circ \operatorname{pi}) \to \operatorname{scal3} B < \operatorname{scal3} A)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.claim` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Conjecture 4.2 (printed p. 11): “Suppose n ≥ 2. For the function Scalₚ(·): D¹ₙ → R one has the following properties: - if p ∈ (1, 2) then Scalₚ(·) is a strictly Schur-decreasing function; - if p ∈ (2, +∞] then Scalₚ(·) is a strictly Schur-increasing function.” This statement encodes the p = 3 clause, with faithful complex density matrices, the fixed eigenvalue vector, and strictness away from permutations.

**Theorem 1.6 (scal3_eq_spectral_ratio).**

$$\forall (n : \mathbb{N}) (A : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , (2 \leq n) \to (A \in \operatorname{densityStates} n) \to \operatorname{scal3} A = \operatorname{CubeRootSpectralMonotonicity} . \operatorname{Vector} . \operatorname{lambdaRatio} (\operatorname{eig} A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The intrinsic coordinate curvature equals the ratio of cube-root eigenvalue power sums. The normal derivative, Gauss contraction, and real Hermitian Jordan traces give this identity.

**Theorem 1.7 (result).**

$$\forall n : \mathbb{N} , 2 \leq n \to \forall A B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} , A \in \operatorname{densityStates} n \to B \in \operatorname{densityStates} n \to \operatorname{PositiveSimplexGeometryAndMixing} . \operatorname{moreMixed} (\operatorname{eig} A) (\operatorname{eig} B) \to \operatorname{scal3} B \leq \operatorname{scal3} A \land ((\neg \exists \operatorname{pi} : \operatorname{Equiv} . \operatorname{Perm} (\operatorname{Fin} n) , \operatorname{eig} A = \operatorname{eig} B \circ \operatorname{pi}) \to \operatorname{scal3} B < \operatorname{scal3} A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result` (`✓ std3`). ∎

*Resolves.* `Problems/gibilisco-isola-2004-quantum-cube-root-scalar-curvature` (proved) by `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gibilisco-isola-2004-quantum-cube-root-scalar-curvature","declaration_gid":"D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The quantum cube-root pull-back curvature increases under the source majorization order, strictly unless the eigenvalue vectors differ by a permutation.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.claim`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.densityStates`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.eig`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.metric`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.result`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.scal3`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio`
- Dependency: [D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization](CoordinateCurvatureMajorization.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative](HermitianCubeDerivative.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus](HermitianHypersurfaceCalculus.md)
