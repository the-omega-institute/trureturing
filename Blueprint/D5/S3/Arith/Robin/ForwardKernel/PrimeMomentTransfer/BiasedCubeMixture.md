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

A finite weighted mixture of biased cube functionals is a real linear functional. It is positive when the weights are nonnegative, N is positive, and every bias value has absolute value at most sqrt(N).

**Theorem 1.3 (Walsh character formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a character on T, the value is the weighted bias moment of order |T| divided by (sqrt(N)) to the power |T|.

**Theorem 1.4 (Distinct-index mixture moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_distinct_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_distinct_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of bias values and weights, the distinct-index moment of order r is the weighted r-th bias moment divided by (sqrt(N)) to the power r, times the sum of coefficient products over injective index tuples. Both refutations apply this shared identity.

**Theorem 1.5 (Odd-coordinate reduction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeated sign factors cancel in pairs, leaving exactly the coordinates with odd multiplicity.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixtureFunctional`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_character`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.mixture_distinct_moments`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.odd_reduction`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.sign`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
