# Rank-one trace bounds and phase rigidity

## Abstract

A sharp unitary trace estimate for rank-one sums and its common-phase equality condition.

**Theorem 1.1 (The unitary trace estimate).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex Euclidean vectors r_j, nonnegative real weights a_j, unit complex phases gamma_j and a unitary matrix V, the norm of Tr(V sum_j a_j gamma_j r_j r_j*) is at most sum_j a_j times the squared norm of r_j. The estimate includes zero weights and zero vectors.

**Theorem 1.2 (Equality forces a common phase).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the weights are strictly positive and every pairwise inner product of the r_j is nonzero. If the unitary trace estimate is an equality, then gamma_i=gamma_j for every i,j. Cauchy–Schwarz equality places each r_j in a unitary eigenspace; nonorthogonality identifies those eigenphases, and equality in the finite triangle inequality identifies the original phases.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq`
