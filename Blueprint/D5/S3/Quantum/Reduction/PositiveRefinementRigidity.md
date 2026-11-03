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

This projection conclusion is an intermediate consequence for positive refinements of a canonical filter. Transferring it to arbitrary complex matrices, singular effects, unequal direct sums, all original finite record branches, and their complete positivity requires the corresponding matrix-span and support bridges. No assertion about an unrelated coarse completely positive map follows from this projection statement.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_projection_scalar`
