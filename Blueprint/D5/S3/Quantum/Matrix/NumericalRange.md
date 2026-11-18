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

**Theorem 1.3 (The unit-spinor Bloch image is on the sphere).**

$$\forall v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right),\; \Vert v\Vert  = 1 \Rightarrow \Vert \operatorname{ActualPureQubitCostInfimum.bloch}(\operatorname{Matrix.vecMulVec}(\operatorname{WithLp.ofLp}(v), \operatorname{star}\left(\operatorname{WithLp.ofLp}(v)\right)))\Vert  = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.blochPure_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer product is Hermitian, has trace one and is idempotent. The existing Hermitian Bloch geometry gives its unit Euclidean norm.

**Theorem 1.4 (Every Bloch sphere point has a unit spinor).**

$$\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \Vert r\Vert  = 1 \Rightarrow \left(\exists v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right),\; \Vert v\Vert  = 1 \land \operatorname{ActualPureQubitCostInfimum.bloch}(\operatorname{Matrix.vecMulVec}(\operatorname{WithLp.ofLp}(v), \operatorname{star}\left(\operatorname{WithLp.ofLp}(v)\right))) = r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.blochPure_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the original all-poles square-root construction: the south pole has its own representative, and every other point uses the nonzero northern denominator.

**Theorem 1.5 (Toeplitz-Hausdorff in finite dimension).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)] \forall A \in E\to_{L}[\mathbb{C}]E,\; \operatorname{Convex}\left(\mathbb{R}, \operatorname{innerNumericalRange}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.finite_numericalRange_convex` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

The span of two vectors has complex dimension at most two. Its compressed operator has a convex numerical range, and the inclusion preserves both expectations.

**Definition 1.6 (Expectations restricted to a subspace).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), K \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{subspaceNumericalRange}\left(A, K\right) = \{z:\mathbb{C}\mid\exists v \in K,\; \Vert v\Vert  = 1 \land z = \operatorname{inner}\left(\mathbb{C}, \operatorname{val}\left(v\right), \operatorname{Matrix.toEuclideanLin}(A)(\operatorname{val}\left(v\right))\right)\}$$

*Formalization.* `D5/S3/Quantum/Matrix/NumericalRange.subspaceNumericalRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector is in K and is coerced to the ambient Euclidean space for the expectation.

**Theorem 1.7 (Every compressed numerical range is convex).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), K \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{Convex}\left(\mathbb{R}, \operatorname{subspaceNumericalRange}\left(A, K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NumericalRange.subspace_numericalRange_convex` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

An orthonormal basis identifies the subspace with a finite Euclidean space; compression preserves the complex expectation.

## Application: the unit-spinor phase quotient

Let U be the subset of EuclideanSpace C (Fin 2) defined by normSq(a)+normSq(b)=1, and let V be the subset of EuclideanSpace R (Fin 3) defined by q(0)^2+q(1)^2+q(2)^2=1. Both carry their inherited standard Euclidean topology. U is the Euclidean three-sphere; the unit sphere for the default maximum norm on C x C is a different subset. The finite WithLp coordinate homeomorphism identifies the coordinate descriptions without changing either subset topology.

On every representative (a,b), define H(a,b)=(2 Re(conj(a)b), 2 Im(conj(a)b), normSq(a)-normSq(b)). This is exactly bloch(vecMulVec v (star v)): the off-diagonal entry is a conj(b), and the minus sign in bloch's imaginary coordinate changes it to the displayed positive 2 Im(conj(a)b). The equality normSq(a)+normSq(b)=1 is equivalent to the Euclidean norm equation norm(v)=1, and the analogous sum-of-squares equation is equivalent to norm(q)=1. Therefore blochPure_norm places H in V, and blochPure_surjective supplies a representative for every point of V, including both poles.

Convert v in U to the existing Ket (Fin 2) with vec=v.ofLp and its same sum-of-squared-norms normalization proof. Pull back Ket.PhaseEquiv along this conversion. The resulting relation is precisely: v is equivalent to w if and only if there is one common c in C with normSq(c)=1 and v(i)=c w(i) for both coordinates i. No separate phase on each coordinate is allowed. Give the resulting Quotient its standard quotient topology.

MState.pure of that ket has matrix vecMulVec v (star v). The first component of bloch_geometry_of_isHermitian reconstructs this matrix as blochMatrix 1 (H(v)); its trace is one. Equal H values thus give equal pure matrices and equal MState values. Conversely equal pure states give equal H values. MState.PhaseEquiv_iff_pure_eq, equivalently MState.pure_eq_pure_iff, identifies these fibers with exactly the pulled-back common unit-complex phase relation. This uses the original normalized-ket fiber theorem rather than a new phase-extraction proof.

The quadratic map H is continuous by finite-coordinate polynomial continuity, complex conjugation and real/imaginary projection. Quotient.lift therefore induces a continuous map from U modulo the common phase to V. The exact fiber equivalence makes it injective, and the original all-poles Bloch supplier makes it surjective. Equiv.ofBijective supplies the inverse set map and both inverse laws. U is a compact Euclidean unit sphere, its quotient is compact, and V is Hausdorff. Pinned Mathlib Continuous.homeoOfEquivCompactToT2 upgrades this same map to a homeomorphism, proving inverse continuity without assuming it. Its value on every quotient representative remains the displayed H formula.

The normalized unit-spinor phase quotient homeomorphism is a consequence of these existing local suppliers and the standard compact-to-Hausdorff theorem. Its scope does not include the full nonzero scaled quotient, classification of phase-invariant polynomials, physical preparation or compression protocols, or absence of a continuous global section. Those stronger conclusions require separate arguments.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.blochPure_norm`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.blochPure_surjective`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.finite_numericalRange_convex`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.innerNumericalRange`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.sphere_image_eq_ball_image`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.subspaceNumericalRange`
- Truth anchor: `D5/S3/Quantum/Matrix/NumericalRange.subspace_numericalRange_convex`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
