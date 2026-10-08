# Cartesian variance

## Abstract

A pure vector maximizes the Cartesian matrix variance.

**Theorem 1.1 (Frobenius square in coordinates).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{RHLinalg.frobSq}(A) = \sum_{i:\operatorname{Fin}\left(n\right)}(\sum_{j:\operatorname{Fin}\left(n\right)}(\operatorname{Complex.normSq}(A(j, i))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared Frobenius norm is the sum of the squared moduli of all matrix entries.

**Theorem 1.2 (Nonnegative Frobenius square).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; 0 \le \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry contributes a nonnegative square.

**Definition 1.3 (Matrix Hilbert-space coordinates).**

$$\forall n \in \mathbb{N},\; \operatorname{vectorize}\left(n\right) = \operatorname{LinearEquiv.trans}(\operatorname{LinearEquiv.symm}(\operatorname{LinearEquiv.curry}(\mathbb{C}, \mathbb{C}, \operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right))), \operatorname{LinearEquiv.symm}(\operatorname{WithLp.linearEquiv}(2, \mathbb{C}, (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\to\mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Matrix/CartesianVariance.vectorize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This complex linear equivalence arranges matrix entries by their ordered pair of indices. It composes Mathlib's inverse currying equivalence with the inverse WithLp linear equivalence.

**Theorem 1.4 (Vectorization preserves the Frobenius square).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\Vert \operatorname{vectorize}\left(n, A\right)\Vert )^{2} = \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.vectorize_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euclidean norm sums the same entries.

**Definition 1.5 (Cartesian variance).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{variance}\left(A, rho\right) = \operatorname{Complex.re}(\operatorname{Matrix.trace}(rho \cdot (\frac{1}{2}\cdot(\operatorname{Matrix.conjTranspose}(A) \cdot A + A \cdot \operatorname{Matrix.conjTranspose}(A))))) - \operatorname{Complex.normSq}(\operatorname{Matrix.trace}(rho \cdot A))$$

*Formalization.* `D5/S3/Quantum/Matrix/CartesianVariance.variance` (`✓ std3`).

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

“Each modulus builds a different variance, which we’ll distinguish by the corresponding subscript too.” Equation (27), page 17, reads Var∗(X) = Tr[ρ|X|²∗] − |Tr[ρX]|², with subscript C giving |X|²C = (X∗X + XX∗)/2. Here X is A, and the real part makes the real-valued trace explicit.

**Definition 1.6 (Cartesian quadratic matrix).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{cartesian}\left(A\right) = \frac{1}{2}\cdot(\operatorname{Matrix.conjTranspose}(A) \cdot A + A \cdot \operatorname{Matrix.conjTranspose}(A))$$

*Formalization.* `D5/S3/Quantum/Matrix/CartesianVariance.cartesian` (`✓ std3`).

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

“For that reason we need a name for the expression ((X∗X + XX∗)/2)1/2, and we have chosen to call it the Cartesian modulus.” (page 17). This definition is the square of that modulus, the literal average of the two Gram matrices.

**Theorem 1.7 (A pure vector attains the density maximum).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; 0 < n \Rightarrow \left(\exists v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right),\; \Vert v\Vert  = 1 \land \left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \left(\operatorname{Matrix.PosSemidef}(rho) \land \operatorname{Matrix.trace}(rho) = 1\right) \Rightarrow \operatorname{variance}\left(A, rho\right) \le \operatorname{variance}\left(A, \operatorname{Matrix.vecMulVec}(\operatorname{WithLp.ofLp}(v), \operatorname{star}\left(\operatorname{WithLp.ofLp}(v)\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.pure_variance_maximizer` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2009). *Variance bounds, with an application to norm bounds for commutators*. URL: <https://arxiv.org/abs/0907.3913>.

*Commentary.*

A compact density set supplies a maximum. First-order optimality gives a linear Hermitian maximum; Toeplitz-Hausdorff on its top eigenspace preserves the complex mean while selecting a unit vector.

**Theorem 1.8 (Hilbert-space trace pairing).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{inner}\left(\mathbb{C}, \operatorname{vectorize}\left(n, A\right), \operatorname{vectorize}\left(n, B\right)\right) = \operatorname{Matrix.trace}(\operatorname{Matrix.conjTranspose}(A) \cdot B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.matrix_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vectorization realizes the trace inner product.

**Theorem 1.9 (Conjugate-transpose invariance).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{RHLinalg.frobSq}(\operatorname{Matrix.conjTranspose}(A)) = \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation preserves squared moduli and transpose permutes entries.

**Theorem 1.10 (Trace-product Cauchy-Schwarz).**

$$\forall n \in \mathbb{N}, Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{Complex.normSq}(\operatorname{Matrix.trace}(Q \cdot B)) \le \operatorname{RHLinalg.frobSq}(Q) \cdot \operatorname{RHLinalg.frobSq}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.trace_product_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply Hilbert-space Cauchy-Schwarz to Q conjugateTranspose and B.

**Theorem 1.11 (The pure maximum bounds every commutator).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), v \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right),\; \left(\Vert v\Vert  = 1 \land \left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \left(\operatorname{Matrix.PosSemidef}(rho) \land \operatorname{Matrix.trace}(rho) = 1\right) \Rightarrow \operatorname{variance}\left(A, rho\right) \le \operatorname{variance}\left(A, \operatorname{Matrix.vecMulVec}(\operatorname{WithLp.ofLp}(v), \operatorname{star}\left(\operatorname{WithLp.ofLp}(v)\right))\right)\right)\right) \Rightarrow \left(\forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{RHLinalg.frobSq}(\operatorname{commutator}\left(A, B\right)) \le 4 \cdot \operatorname{RHLinalg.frobSq}(B) \cdot \operatorname{variance}\left(A, \operatorname{Matrix.vecMulVec}(\operatorname{WithLp.ofLp}(v), \operatorname{star}\left(\operatorname{WithLp.ofLp}(v)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianVariance.commutator_pure_max_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero B its two Gram matrices, normalized by twice the Frobenius square, form a density matrix. The commutator variance bound applies to this common density; B equal to zero is included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.cartesian`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.commutator_pure_max_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_eq_sum`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.frobSq_star`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.matrix_pairing`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.pure_variance_maximizer`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.trace_product_cauchy`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.variance`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.vectorize`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianVariance.vectorize_norm_sq`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../../Observer/HiddenFlow/ProjectionCommutatorIdentity.md)
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../BlockNorm/EssentiallyHermitian.md)
- Dependency: [D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth](../Entanglement/UniversalReplacementCapacityGrowth.md)
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../Fibers/PhysicalFiber.md)
- Dependency: [D5/S3/Quantum/Matrix/NumericalRange](NumericalRange.md)
