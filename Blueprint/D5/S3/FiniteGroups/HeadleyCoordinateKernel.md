# Cyclic kernels and the exponent measure

## Abstract

Cyclic kernels and the exponent measure

**Definition 1.1 (Reduction modulo two).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction`

*Formalization.* `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive cyclic two-primary coordinate maps onto ZMod 2 by the canonical reduction homomorphism. Exponent zero is excluded only from the two coordinates selected for reduction.

**Theorem 1.2 (The reduction kernel is the doubled range).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction_kernel_eq_doubled`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction_kernel_eq_doubled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction kills exactly twice the elements of the original cyclic coordinate. For exponent one both sides are the trivial subgroup.

**Definition 1.3 (The actual decremented kernel type).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reductionKernelEquiv`

*Formalization.* `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reductionKernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cyclic subgroup classification identifies the literal kernel with ZMod of two to the preceding exponent. The identification uses its cardinality and includes the trivial kernel.

**Theorem 1.4 (Strict decrease by two).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.lower_sum_add_two`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyCoordinateKernel.lower_sum_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lowering two distinct positive entries removes exactly two from their sum. Entries outside this pair remain fixed, including zero entries.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.lower_sum_add_two`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reductionKernelEquiv`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction_kernel_eq_doubled`
