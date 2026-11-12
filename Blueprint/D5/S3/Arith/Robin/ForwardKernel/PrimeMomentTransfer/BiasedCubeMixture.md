# Biased Boolean cube mixtures

## Abstract

Finite mixtures of biased Boolean cubes have explicit Walsh characters and parity reductions.

**Definition 1.1 (Boolean sign).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.sign`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.sign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign map sends true to one and false to minus one.

**Definition 1.2 (Finite biased cube mixture).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixtureFunctional`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixtureFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite nonnegative mixture of product sign measures is represented as a real linear functional.

**Theorem 1.3 (Walsh character formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value on a Walsh character is the weighted moment of the bias divided by the coordinate square root.

**Theorem 1.4 (Odd-coordinate reduction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeated sign factors cancel in pairs, leaving exactly the coordinates with odd multiplicity.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixtureFunctional`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.sign`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
