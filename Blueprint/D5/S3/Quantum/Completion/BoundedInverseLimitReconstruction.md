# Bounded Inverse-Limit Reconstruction

## Abstract

Bounded compatible projection families reconstruct the cumulative Hilbert completion.

**Theorem 1.1 (Bounded compatible families reconstruct the cumulative completion).**

$$\begin{gathered}\forall k, H: \operatorname{Type},\\{}[\operatorname{RCLike}(k)], [\operatorname{NormedAddCommGroup}(H)],\\{}[\operatorname{InnerProductSpace}(k, H)], [\operatorname{CompleteSpace}(H)],\\{}S: \mathbb{N} \to \operatorname{Submodule}(k, H),\\{}[\forall n: \mathbb{N}, \operatorname{HasOrthogonalProjection}(S(n))],\\{}hS: \operatorname{Monotone}(S),\\{}\operatorname{Isometry}((\operatorname{canonicalReconstructionEquiv}(S, hS): \operatorname{cumulativeSpace}(S) \to \operatorname{boundedInverseLimit}(S))) \land \operatorname{Bijective}((\operatorname{canonicalReconstructionEquiv}(S, hS): \operatorname{cumulativeSpace}(S) \to \operatorname{boundedInverseLimit}(S))) \land (\forall x: \operatorname{cumulativeSpace}(S), \forall n: \mathbb{N},\ ((\operatorname{canonicalReconstructionEquiv}(S, hS)(x): \operatorname{boundedInverseLimit}(S)): \operatorname{BoundedContinuousFunction}(\mathbb{N}, H))(n) = \operatorname{starProjection}(S(n), (x: H))) \land\\{}\operatorname{Isometry}((\operatorname{quotientReconstructionEquiv}(S, hS): \operatorname{Quotient}(H, \operatorname{residualSpace}(S)) \to \operatorname{boundedInverseLimit}(S))) \land \operatorname{Bijective}((\operatorname{quotientReconstructionEquiv}(S, hS): \operatorname{Quotient}(H, \operatorname{residualSpace}(S)) \to \operatorname{boundedInverseLimit}(S))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.bounded_inverse_limit_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a monotone sequence of closed subspaces of a complete Hilbert space. Its bounded inverse limit is constructed as the subspace of bounded families x_n with x_n in S_n and with every earlier coordinate equal to the orthogonal projection of every later one.

The canonical map J sends x in the closure of the union of the stages to the family of its orthogonal projections. Increasing projection convergence proves that J preserves the norm. Conversely, projection compatibility gives a Pythagorean identity for coordinate differences; bounded squared norms therefore make every compatible family Cauchy.

The family limit lies in the cumulative closure and has exactly the given stage projections, proving bijectivity. The quotient conclusion is obtained by composing J with Mathlib's canonical isometry from the quotient by the residual orthogonal complement to the cumulative space.

## References

- Truth anchor: `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.bounded_inverse_limit_reconstruction`
