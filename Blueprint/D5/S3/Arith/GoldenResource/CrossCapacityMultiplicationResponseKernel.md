# Cross-Capacity Multiplication Response Kernels

## Abstract

Cross-Capacity Multiplication Response Kernels.

**Theorem 1.1 (Equality of all multiplication responses).**

Lean statement: `D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel.eq_plus_all_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel.eq_plus_all_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two natural capacity vectors on a common finite coordinate set and a bounded state in each box. Each letter increases its coordinate by one and fails at capacity. A successful word returns the parity sign of the endpoint coordinate sum when every coordinate is at most one, and zero otherwise; failure is a distinct value. The states agree on every finite word, including the empty word, exactly when their remaining capacities agree and one of two conditions holds. Either both initial states are not squarefree, or both are squarefree, their coordinate sums have equal parity, and their coordinates agree on every axis of positive remaining capacity. Repeated letters recover the entire remaining capacity on each axis. In the squarefree branch, on successful words, coordinates with zero remaining capacity stay fixed and contribute only their initial parity, while all other coordinates increase together. Zero capacities and an empty coordinate set are allowed.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel.eq_plus_all_iff`
- Dependency: [D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel](FiniteMultiplicationResponseKernel.md)
