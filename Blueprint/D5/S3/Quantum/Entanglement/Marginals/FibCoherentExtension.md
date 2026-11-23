# Coherent Fibonacci marginal extensions

## Abstract

A common-state criterion for two adjacent Fibonacci marginals with arbitrary coherences.

**Theorem 1.1 (The residual endpoint marginals).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five legal Fibonacci words split into the middle singleton and the four occupation patterns of the two endpoints. Let b be the weight of the singleton and let L and R be the two observed endpoint blocks, obtained by restricting each edge matrix to the empty-middle subspace. Both edges supply the same middle-to-vacuum entry. Each edge supplies one additional middle-to-endpoint entry. The middle-to-double-occupation entry is free.

A common positive semidefinite trace-one state exists exactly when b is nonnegative, the two endpoint block traces both equal 1 - b, and there is a choice of the free entry for which the two residual blocks are positive semidefinite. For positive b the residuals subtract the respective endpoint marginals of the outer product of the conjugated middle row divided by b. At b = 0 the entire row coupling must vanish and the endpoint blocks themselves are the residuals.

The scalar Schur complement gives the necessity of the residual conditions. Their traces agree by trace preservation. If their trace is positive, their tensor product divided by that trace gives a joint positive residual on the endpoints. At trace zero the residual blocks are zero. Restoring the outer product contribution and the middle singleton gives the required common state.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension](FibMarginalExtension.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
