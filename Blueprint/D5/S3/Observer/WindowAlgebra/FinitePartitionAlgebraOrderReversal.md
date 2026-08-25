# Finite Partition Algebra Order Reversal

## Abstract

Finite state-kernel inclusion reverses real effect-algebra inclusion.

**Theorem 1.1 (Smaller state kernels give larger effect algebras).**

$$\forall X, R_{1}, R_{2},\ Finite(X) \land Equivalence(R_{1}) \land Equivalence(R_{2}) \Rightarrow\ (R_{1} \subseteq R_{2} \Leftrightarrow A_{R_{2}} \subseteq A_{R_{1}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraOrderReversal.finite_partition_algebra_order_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite and let R1 and R2 be equivalence relations on X. For each relation R, its effect algebra is constructed as the set of real-valued functions constant on every R-class.

If R1 is contained in R2, every function constant on R2 is constant on R1. Conversely, the existing finite real partition-algebra reconstruction theorem turns reverse algebra inclusion back into the original relation inclusion.

Repository and pinned-Mathlib searches found no exact order-reversal theorem. The proof applies the existing real-carrier reconstruction result directly; no alternate algebra construction is introduced.

## References

- Truth anchor: `D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraOrderReversal.finite_partition_algebra_order_reversal`
- Dependency: [D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence](FinitePartitionAlgebraAntiequivalence.md)
