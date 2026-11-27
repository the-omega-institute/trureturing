# Dyadic traces and minus-sided affine covariance

## Abstract

The dyadic tracial bicommutant is a factor, with faithful normalized vacuum trace. The minus-sided affine group acts unitarily on the Lebesgue Hilbert space.

**Theorem 1.1 (Uniqueness of the normalized trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.normalizedTrace_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.normalizedTrace_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive matrix size, cyclicity kills off-diagonal matrix units and equates the values on diagonal units. Normalization fixes their common value at the reciprocal of the matrix size. Linear expansion in matrix units determines the entire functional.

**Theorem 1.2 (Trace preserved by tensoring with the identity).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{MatrixLevel}\left(n\right),\; \operatorname{normalizedTrace}\left(2^{n + 1}, \operatorname{embed}\left(n, a\right)\right) = \operatorname{normalizedTrace}\left(2^{n}, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.normalizedTrace_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At level n, the algebra embedding sends a matrix to its Kronecker product with the two-dimensional identity. Tensoring doubles the ordinary trace and the dimension. Reindexing preserves the diagonal sum.

**Theorem 1.3 (Projection equivalence by normalized trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.projection_equiv_iff_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.projection_equiv_iff_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian projection diagonalizes in a unitary eigenbasis. Idempotence gives only zero and one as eigenvalues. The normalized trace counts the ones divided by the matrix size. Thus equal trace gives a common cutoff diagonal and a unitary conjugating one projection to the other. Cyclicity gives the converse.

**Theorem 1.4 (Faithful normalized trace on the algebraic limit).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.algTrace_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.algTrace_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compatible functionals descend to the direct limit. Products are computed in a common matrix algebra, where the finite trace is cyclic. The trace of a star square is nonnegative and vanishes exactly when the element is zero.

**Theorem 1.5 (Scalar center of the algebraic limit).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_center_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_center_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Represent a central element in one matrix algebra. Injectivity of the inclusion reflects commutation with that algebra's matrix units. The off-diagonal entries then vanish and all diagonal entries agree.

**Theorem 1.6 (Exact projection dimensions in the algebraic limit).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_projection_trace_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_projection_trace_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A projection in the limit has a matrix representative that is itself a projection, by injectivity and preservation of star. In dimension 2ⁿ, every integer rank from zero through 2ⁿ occurs as a diagonal cutoff and has normalized trace k/2ⁿ.

**Theorem 1.7 (Density in the unit interval).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicTrace_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicTrace_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real number in [0,1], divide the floor of its product with 2ⁿ by 2ⁿ. The error lies between zero and 2⁻ⁿ, so these dyadic projection values converge to the given number.

**Theorem 1.8 (Faithful tracial vacuum functional).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete the algebra in the norm from its trace inner product and take the bicommutant of left multiplication. Right multiplication commutes with it and its translates of the vacuum are dense, so the vacuum is separating. The antiunitary extension of star sends the vector obtained from a bicommutant operator to the vector obtained from its adjoint. This yields cyclicity, and the expectation of a star square is its vacuum norm squared.

**Theorem 1.9 (Normality of the vacuum trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded increasing positive net, each vector expectation increases to a finite limit. The square of the norm of an operator increment on a vector is bounded by the scalar operator bound times the corresponding expectation increment. This gives pointwise convergence to a bounded operator that still commutes with the centralizer. The limit is the operator supremum, and evaluating it at the vacuum gives the supremum of the trace values.

**Theorem 1.10 (Faithful matrix inclusions in the bicommutant).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.representedMatrix_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.representedMatrix_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left multiplication embeds each matrix algebra into the tracial bicommutant. The inclusions are injective, preserve the trace, and are compatible with the forward embeddings.

**Theorem 1.11 (Strong density of the increasing matrix algebras).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.matrix_tower_strongly_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.matrix_tower_strongly_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of vectors, the closure of its orbit under diagonal left multiplication has an orthogonal projection. Every matrix entry of this projection commutes with left multiplication, so a bicommutant operator preserves that orbit closure. A single element of the algebraic limit approximates the operator on the whole finite family, and that element belongs to one matrix algebra.

**Theorem 1.12 (All real projection dimensions in the unit interval).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_projection_trace_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_projection_trace_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a given number in [0,1], the dyadic cutoff projections form an increasing sequence under the inclusions. Its strong limit is a projection, and its trace is the limit of the dyadic dimensions. Positivity of a projection and of its complement bounds every projection trace between zero and one.

**Theorem 1.13 (Scalar center in the Hilbert completion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_center_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_center_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a central bounded operator z, the functional a ↦ ⟨Ω,z L(a)Ω⟩ on the algebraic limit is cyclic. Subtract its value on the identity times the normalized trace. Uniqueness forces the difference to vanish. Density and the separating vacuum then identify z with the corresponding scalar operator.

**Theorem 1.14 (Minus-sided unitary operators).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSidedAction_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSidedAction_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For affine coordinates s and a, write λ=exp(−2πs). The unitary operator sends f to λ⁻¹ᐟ² f((x+a)/λ) almost everywhere. The Jacobian of the affine coordinate change cancels the square of its normalization. The affine inverse gives the inverse unitary. In exponential coordinates the same formula is exp(πs) f(exp(2πs)(x+a)).

**Theorem 1.15 (Minus-sided affine covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSided_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSided_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hans-Jürgen Borchers (1992). *The CPT-theorem in two-dimensional theories of local observables*. DOI: [10.1007/BF02099011](https://doi.org/10.1007/BF02099011). URL: <https://doi.org/10.1007/BF02099011>.

*Commentary.*

The group law sends pairs (s,a),(t,b) to (s+t,a+exp(−2πs)b). Conjugating translation by dilation multiplies its parameter by exp(−2πs), which is at least one at nonpositive modular time. The faithful real matrix representation has first row (exp(−2πs),a) and second row (0,1). In Fourier coordinates the translation generator multiplies by 2πξ. On nonnegative frequencies its spectrum is the nonnegative real half-line. On the common Schwartz domain the dilation and translation generators have commutator −2πiP.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.algTrace_spec`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_center_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.alg_projection_trace_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_center_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.completed_projection_trace_range`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicTrace_closure`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_normal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.dyadicVacuumTrace_spec`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.matrix_tower_strongly_dense`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSidedAction_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.minusSided_covariance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.normalizedTrace_embed`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.normalizedTrace_unique`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.projection_equiv_iff_trace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.representedMatrix_spec`
