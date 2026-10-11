# All-source sparse cut recovery classification

## Abstract

Common-suffix recutting exactly classifies recovery of complete literal rows.

**Theorem 1.1 (Full common-suffix classification).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite prefix-free P and Q, a unique factor from the realized image of canonicalRow P to that of canonicalRow Q exists exactly when P = Q S for some finite prefix-free S. The result also includes the explicit finite decoder, the executable Boolean criterion, uniqueness of S when Q is nonempty, all four empty/root boundaries, concrete absent-cut guards, and equivalence with the independently computed exterior-plus-partition record.

Necessity first uses the uncovered-hole native pair to obtain prefix coverage. If two Q sections differ, the simultaneous one-class marker pair contradicts recovery; therefore every section is the same finite suffix. Sufficiency uses the finite source-free decoder. The realized-image factorization step directly applies realized_image_unique_factorization_iff_reverse_kernel. Empty P recovers every Q; empty Q requires empty P; root Q is recovered by every P; root P recovers only root Q. The scope remains all finite nonempty ordered Boolean trees, including absent cuts. The conclusion concerns the original row maps and makes no bounded-budget, physical execution, or broader calibration assertion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionClassification.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder](ActualCutPartitionDecoder.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization](../../../ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.md)
