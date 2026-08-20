# Bounded Inverse-Limit Reconstruction

## Abstract

Bounded compatible projection families reconstruct the cumulative Hilbert completion.

**Theorem 1.1 (Bounded compatible families reconstruct the cumulative completion).**

$$\forall k: \operatorname{RCLikeField}(),\ \forall H: \operatorname{CompleteHilbertSpace}(k),\ \forall S: \operatorname{Sequence}(\operatorname{Submodule}(k, H)),\ \operatorname{Monotone}(S) \land \operatorname{HasOrthogonalProjection}(S),\ Sinfinity = \operatorname{ClosureUnion}(S),\ Rinfinity = \operatorname{OrthogonalComplement}(Sinfinity),\ J: Sinfinity \to \operatorname{BoundedInverseLimit}(S),\ Q: \operatorname{Quotient}(H, Rinfinity) \to \operatorname{BoundedInverseLimit}(S),\ \operatorname{Isometry}(J) \land \operatorname{Bijective}(J) \land (\forall x \in Sinfinity, \forall n \in \mathbb{N},\ \operatorname{coord}(\operatorname{apply}(J, x), n) = \operatorname{orthogonalProjection}(\operatorname{apply}(S, n), x)) \land \operatorname{Isometry}(Q) \land \operatorname{Bijective}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.bounded_inverse_limit_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a monotone sequence of closed subspaces of a complete Hilbert space. Its bounded inverse limit is constructed as the subspace of bounded families x_n with x_n in S_n and with every earlier coordinate equal to the orthogonal projection of every later one.

The canonical map J sends x in the closure of the union of the stages to the family of its orthogonal projections. Increasing projection convergence proves that J preserves the norm. Conversely, projection compatibility gives a Pythagorean identity for coordinate differences; bounded squared norms therefore make every compatible family Cauchy.

The family limit lies in the cumulative closure and has exactly the given stage projections, proving bijectivity. The quotient conclusion is obtained by composing J with Mathlib's canonical isometry from the quotient by the residual orthogonal complement to the cumulative space.

## References

- Truth anchor: `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.bounded_inverse_limit_reconstruction`
