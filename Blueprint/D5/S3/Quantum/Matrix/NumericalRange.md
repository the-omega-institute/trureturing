# Numerical ranges and compression

## Abstract

Numerical ranges are convex under finite-dimensional compression.

**Theorem 1.1 (An invisible direction reaches the sphere).**

$$\forall E \in Type, F \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{AddCommGroup}\left(F\right)] [\operatorname{Module}\left(\mathbb{R}, F\right)] \forall L \in E\to_{l}[\mathbb{R}]F, k \in E,\; \left(k \ne 0 \land L(k) = 0\right) \Rightarrow \operatorname{Set.image}(L, \operatorname{Metric.sphere}(0, 1)) = \operatorname{Set.image}(L, \operatorname{Metric.closedBall}(0, 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.sphere_image_eq_ball_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero kernel direction carries every point in the closed unit ball to the unit sphere without changing its linear image.

**Definition 1.2 (Inner-product numerical range).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] \forall A \in E\to_{L}[\mathbb{C}]E,\; \operatorname{innerNumericalRange}\left(A\right) = \{z:\mathbb{C}\mid\exists v \in E,\; \Vert v\Vert  = 1 \land z = \operatorname{inner}\left(\mathbb{C}, v, A(v)\right)\}$$

*Formalization.* `D5/S3/Quantum/Matrix/NumericalRange.innerNumericalRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The values are complex expectations on unit vectors. The inner product is conjugate-linear in its first argument.

**Theorem 1.3 (Toeplitz-Hausdorff in finite dimension).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)] \forall A \in E\to_{L}[\mathbb{C}]E,\; \operatorname{Convex}\left(\mathbb{R}, \operatorname{innerNumericalRange}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.finite_numericalRange_convex` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

The span of two vectors has complex dimension at most two. Its compressed operator has a convex numerical range, and the inclusion preserves both expectations.

**Definition 1.4 (Expectations restricted to a subspace).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), K \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{subspaceNumericalRange}\left(A, K\right) = \{z:\mathbb{C}\mid\exists v \in K,\; \Vert v\Vert  = 1 \land z = \operatorname{inner}\left(\mathbb{C}, \operatorname{val}\left(v\right), \operatorname{Matrix.toEuclideanLin}(A)(\operatorname{val}\left(v\right))\right)\}$$

*Formalization.* `D5/S3/Quantum/Matrix/NumericalRange.subspaceNumericalRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector is in K and is coerced to the ambient Euclidean space for the expectation.

**Theorem 1.5 (Every compressed numerical range is convex).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), K \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{Convex}\left(\mathbb{R}, \operatorname{subspaceNumericalRange}\left(A, K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.subspace_numericalRange_convex` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

An orthonormal basis identifies the subspace with a finite Euclidean space; compression preserves the complex expectation.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.finite_numericalRange_convex`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.innerNumericalRange`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.sphere_image_eq_ball_image`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.subspaceNumericalRange`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.subspace_numericalRange_convex`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
