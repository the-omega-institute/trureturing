# Unique Minimal Target Completion

## Abstract

A projection residual generates the unique minimal closed target completion.

**Theorem 1.1 (The residual line is the unique minimal completion).**

$$\forall k: \operatorname{RCLike}, \forall H: \operatorname{Hilbert}(k), \forall M: \operatorname{ClosedSubspace}(H), \forall x\in H, r = x - P_M(x), M_* = M + \operatorname{span}(\{r\}), \operatorname{Disjoint}(M, \operatorname{span}(\{r\})) \land \operatorname{IsLeast}(M_*, \{N: \operatorname{ClosedSubspace}(H) | M \subseteq N \land x\in N\}) \land (r \neq 0 \Rightarrow \operatorname{dim}(M_*/M) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/UniqueMinimalTargetCompletion.unique_minimal_target_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a closed subspace of a complete real-or-complex inner-product space and let x be a target vector. The residual is constructed from the canonical orthogonal projection.

The residual line is disjoint from M, and their sum is the least closed subspace containing both M and x. This least-property states the claimed uniqueness rather than merely exhibiting a containing subspace.

When the residual is nonzero, the canonical relative quotient of the completion by M has dimension one. The proof directly uses the projection residual lemma, closed finite-dimensional sums, the second isomorphism law, and the dimension of a nonzero line.

## References

- Truth anchor: `D5/S3/Quantum/Completion/UniqueMinimalTargetCompletion.unique_minimal_target_completion`
- Dependency: [D5/S3/Quantum/Completion/RelativeQuotientDecomposition](RelativeQuotientDecomposition.md)
