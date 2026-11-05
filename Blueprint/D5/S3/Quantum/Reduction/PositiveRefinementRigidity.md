# Positive refinement rigidity

## Abstract

Positive domination by identity determines one scalar on all orthogonal projections.

Let Phi be a complex linear endomorphism of the matrices on an arbitrary finite coordinate type. Assume positivity on every positive semidefinite input and the Loewner inequality Phi(X) less than or equal to X on those same inputs. Complete positivity and a Kraus representation are not hypotheses. A chosen coordinate certifies that the matrix algebra is nonzero.

**Theorem 1.1 (A common scalar for every projection).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{Nonempty}\left(n\right)] \forall f \in \operatorname{ComplexLinearMap}\left(\operatorname{Matrix}\left(n, n, \mathbb{C}\right), \operatorname{Matrix}\left(n, n, \mathbb{C}\right)\right),\; {\forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{PSD}\left(X\right) \implies \operatorname{PSD}\left(f(X)\right)} \land {\forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{PSD}\left(X\right) \implies f(X)\le X} \implies \exists c\in \mathbb{R}, 0\le c\le 1 \land f(I)=cI \land \forall P \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; P^{*}=P \land PP=P \implies f(P)=cP$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_projection_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a real scalar c between zero and one such that Phi(I) is cI and Phi(P) is cP for every Hermitian idempotent P. The scalar is the chosen diagonal entry of Phi(I). Zero projections and one dimensional algebras are included.

For a projection P, positivity and domination put Phi(P) in the corner of P and Phi(I minus P) in its orthogonal corner. Their sum is Phi(I), which therefore commutes with P and has Phi(P) as its compression. Coordinate projections make Phi(I) diagonal. The projection onto the sum of any two distinct coordinate vectors equates the corresponding diagonal entries. Positivity of Phi(I) and I minus Phi(I) bounds the common entry.

This projection conclusion is an intermediate consequence for positive refinements of a canonical filter. The matrix-span and positive compression results below extend this conclusion and identify input kernel directions and original direct-sum centers. The complete singular scalar formula and the complete positivity of all original records require their full support-corner application. No assertion about an unrelated coarse completely positive map follows from this projection statement.

**Theorem 1.2 (Projections determine a complex linear matrix map).**

Lean statement: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.eq_of_projection_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.eq_of_projection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite decidable coordinate type n and any complex module V with an additive commutative group, two complex linear maps from M_n(C) to V are equal if they agree on every Hermitian idempotent. Unitary diagonalization expresses every Hermitian matrix as a linear combination of orthogonal projections. Real and imaginary self-adjoint parts then give every complex matrix. Empty coordinate types are included.

**Theorem 1.3 (Scalar action on every complex matrix).**

Lean statement: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite decidable coordinate type n with a chosen coordinate, let Phi be a complex linear matrix endomorphism. If Phi maps every PSD input to a PSD matrix and Phi(X) is at most X on every PSD input, there exists a real c with zero at most c at most one such that Phi(X)=c X for every complex matrix X. Positivity is the only map-positivity premise.

**Theorem 1.4 (A vanished projection removes its cross terms).**

Lean statement: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.positive_map_projection_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.positive_map_projection_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite decidable input and output coordinate types n and m, let Phi:M_n(C) to M_m(C) be complex linear and positive on every PSD input. For every Hermitian idempotent P, if Phi(I-P)=0, then Phi(P X P)=Phi(X) for every complex matrix X. Positive output trace functionals and Cauchy-Schwarz remove both cross terms. Complete positivity is not assumed.

**Theorem 1.5 (Original labels preserve the unequal direct-sum centers).**

Lean statement: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.canonical_refinement_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.canonical_refinement_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any finite set of original fine records, B any finite decidable set of centers, and d(b) arbitrary finite decidable coordinate types, without an equal-dimension assumption. Let R(b) be square complex matrices and S(a) complex linear endomorphisms of the product of the matrix blocks. Assume each S(a) maps every componentwise PSD input to a componentwise PSD output and, for every input X and center b, the sum over the same labels a of S(a)(X)(b) equals R(b) X(b) R(b)*. Then S(a)(X)(b) equals S(a) applied to the input with only block b retained, evaluated at b. If R(b)=0, that output vanishes for every X. For every Hermitian idempotent P in block b with R(b) P=R(b), replacing the single input block X by P X P leaves that output unchanged. Zero blocks and empty finite carriers are included. No fine record is replaced by a Kraus index.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.canonical_refinement_structure`
- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.eq_of_projection_eq`
- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_projection_scalar`
- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_scalar`
- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.positive_map_projection_compression`
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
