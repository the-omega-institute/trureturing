# Real conjugation and operator restriction

## Abstract

The fixed real Hilbert space of a conjugation and the transport of bounded operators and Hilbert–Schmidt sums.

An antiunitary involution gives a real form of a complex Hilbert space. Its fixed vectors carry the real Hilbert norm, and each complex vector decomposes uniquely into a fixed real part plus the imaginary unit times a fixed real part.

**Definition 1.1 (Real conjugation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.RealConjugation`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.RealConjugation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A real linear isometric equivalence is involutive and sends a complex scalar multiple to the conjugate scalar times the image vector.

**Definition 1.2 (Fixed real subspace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real submodule is the set of vectors fixed by the conjugation.

**Theorem 1.3 (Closed real form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace_isClosed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The fixed real subspace is closed, since it is the equality set of two continuous maps.

**Definition 1.4 (Real inner product space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceInnerProductSpace`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceInnerProductSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The fixed real subspace inherits the real part of the ambient complex inner product.

**Definition 1.5 (Completeness of the real form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceComplete`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceComplete` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

When the ambient space is complete, the fixed real subspace is complete because it is closed.

**Definition 1.6 (Real part).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real part is one half of the vector plus its conjugate.

**Definition 1.7 (Imaginary part).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The imaginary part is the vector minus its conjugate divided by twice the imaginary unit.

**Theorem 1.8 (Fixed real part).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real part lies in the fixed real subspace.

**Theorem 1.9 (Fixed imaginary part).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The imaginary part lies in the fixed real subspace.

**Theorem 1.10 (Real and imaginary decomposition).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Every vector is the sum of its real part and the imaginary unit times its imaginary part.

**Theorem 1.11 (Uniqueness of the decomposition).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Any decomposition into a fixed real vector plus the imaginary unit times another fixed real vector yields exactly the real and imaginary parts.

**Theorem 1.12 (Antiunitary inner product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conj_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conj_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The complex inner product of two conjugated vectors equals the conjugate of their complex inner product.

**Theorem 1.13 (Inner product of fixed vectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The complex inner product of fixed vectors is the real inner product embedded into the complex numbers.

**Theorem 1.14 (Squared norm decomposition).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.norm_sq_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.norm_sq_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared norm of every vector equals the sum of the squared norms of its real and imaginary parts.

**Definition 1.15 (Conjugate bounded operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Applying the conjugation before and after a bounded complex linear operator defines another bounded complex linear operator.

**Theorem 1.16 (Conjugate operator action).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At each vector the conjugate operator applies the conjugation, the original operator, and the conjugation in order.

**Theorem 1.17 (Conjugation and adjoints).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The adjoint of the conjugate operator equals the conjugate of the adjoint.

**Theorem 1.18 (Conjugation and composition).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_comp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Conjugation preserves operator composition, because the two consecutive involutions cancel.

**Theorem 1.19 (Positivity under conjugation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The conjugate of a nonnegative bounded operator is nonnegative.

**Definition 1.20 (Real operator restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A complex linear bounded operator commuting with the conjugation restricts to a real linear bounded map of the fixed real Hilbert space into itself.

**Theorem 1.21 (Action of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The underlying complex vector of the restriction applied to a fixed vector is its image under the original operator.

**Theorem 1.22 (Equal real and complex norms).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For an operator commuting with the conjugation, the operator norm on the fixed real Hilbert space equals its complex operator norm. The squared norm decomposition transfers the bound from fixed vectors to arbitrary vectors.

**Theorem 1.23 (Reality of the adjoint).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.adjoint_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.adjoint_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If an operator commutes with the conjugation then its adjoint also commutes with it.

**Theorem 1.24 (Adjoint of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Restricting the adjoint to the fixed real Hilbert space gives the adjoint of the real restriction.

**Theorem 1.25 (Self-adjointness of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The restriction of a self-adjoint operator commuting with conjugation is self-adjoint.

**Theorem 1.26 (Positivity of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The restriction of a nonnegative operator commuting with conjugation is nonnegative.

**Theorem 1.27 (Skew-adjointness of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_skewAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_skewAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The restriction of a skew-adjoint operator commuting with conjugation is skew-adjoint.

**Definition 1.28 (Complex Hilbert basis from a real Hilbert basis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The same vectors of any real Hilbert basis of the fixed subspace define a complex Hilbert basis of the ambient space.

**Theorem 1.29 (Identical basis vectors).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Each vector of the complex Hilbert basis is exactly the underlying ambient vector of the corresponding real Hilbert basis.

**Theorem 1.30 (Countable real Hilbert basis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.exists_countable_realHilbertBasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.exists_countable_realHilbertBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a separable ambient complex Hilbert space, the fixed real Hilbert space admits a Hilbert basis on a countable index set.

**Theorem 1.31 (Convergent Hilbert–Schmidt sum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hasSum_hsSq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hasSum_hsSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a Hilbert–Schmidt complex operator commuting with conjugation, the sum of the squared norms of its real restriction along any real Hilbert basis converges to the complex Hilbert–Schmidt squared norm.

**Theorem 1.32 (Preservation of the Hilbert–Schmidt square sum).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hsSq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hsSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a Hilbert–Schmidt complex operator commuting with the conjugation, the squared norm sum of its real restriction along any real Hilbert basis equals the complex Hilbert–Schmidt squared norm.

**Theorem 1.33 (Compactness of the real restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_isCompact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_isCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a Hilbert–Schmidt complex operator commuting with the conjugation, its real restriction is compact.

**Definition 1.34 (Null-diamond real conjugation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.nullDiamondRealConjugation`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.nullDiamondRealConjugation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The isometric frequency-reflection conjugation on the four-dimensional phase Hilbert space supplies a real conjugation, with involution and conjugate scalar law inherited from the frequency action.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.RealConjugation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.adjoint_commutes`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.complexHilbertBasis_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_adjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_comp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conjOp_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.conj_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.exists_countable_realHilbertBasis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.imagPart_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.norm_sq_decomposition`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.nullDiamondRealConjugation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realPart_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceComplete`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspaceInnerProductSpace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.realSubspace_isClosed`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_decomposition`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_imag_unique`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.real_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_adjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hasSum_hsSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_hsSq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_isCompact`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation.restrictReal_skewAdjoint`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Compact](../TraceClass/Compact.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../TraceClass/HilbertSchmidt.md)
