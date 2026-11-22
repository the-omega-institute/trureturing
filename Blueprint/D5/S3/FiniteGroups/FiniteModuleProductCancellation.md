# Finite Module Product Cancellation

## Abstract

Cancelling a common finite module.

**Theorem 1.1 (Cancelling a common finite module).**

Lean statement: `D5/S3/FiniteGroups/FiniteModuleProductCancellation.finite_prod_cancel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteModuleProductCancellation.finite_prod_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Count the linear maps from each finite source to the two products. The common factor cancels in the cardinal counts. Decompose maps by their kernels, then induct on the source size to recover the counts of injective maps. An injection between the remaining factors is bijective because they have the same finite cardinality.

## References

- Truth anchor: `D5/S3/FiniteGroups/FiniteModuleProductCancellation.finite_prod_cancel`
