# Rank-One Context Commutator

## Abstract

Complete normalized rank-one contexts satisfy the aggregate projection commutator formula.

**Theorem 1.1 (Aggregate projection commutator formula).**

$$\operatorname{CompleteNormalizedRankOneContexts}(B, C, d) \land 2 \leq d \Rightarrow\\\operatorname{AggregateCommutatorSquare}(B, C) = 2(d - 1)\operatorname{Incompatibility}(B, C).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RankOneContextCommutator.aggregated_rank_one_context_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B and C be complete normalized rank-one projective contexts in complex dimension d, with d at least two. Each projection is self-adjoint, idempotent, has trace one, and satisfies the rank-one sandwich law; each context resolves the identity.

The squared Hilbert-Schmidt norm is represented by the real part of trace(A* A). The proof applies the exact trace conjugation, cyclicity, finite-sum, and scalar-linearity declarations from the pinned library to obtain the pairwise identity 2 m (1-m), then sums it over both contexts.

Completeness makes the total overlap equal to d. Cancelling the nonzero factor d-1 against the definition of normalized incompatibility gives the displayed formula without fixing a particular dimension or pair of contexts.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/RankOneContextCommutator.aggregated_rank_one_context_commutator`
