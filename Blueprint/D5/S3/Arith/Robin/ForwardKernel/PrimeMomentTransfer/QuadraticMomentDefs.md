# Quadratic moment definitions

## Abstract

Finite quadratic moment sums and pairing expressions.

**Definition 1.1 (Coefficient sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.indexSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.indexSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum a real coefficient function over the finite index type.

**Definition 1.2 (Moment of weighted sums).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply a real linear functional to a product of finite sums of indexed algebra elements weighted by real coefficient functions.

**Definition 1.3 (Distinct-index moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum coefficient products times the linear functional of the corresponding algebra products over ordered injective tuples of indices.

**Definition 1.4 (Perfect pairing sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.perfectPairingSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.perfectPairingSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a function of two coefficient functions, sum its three products associated with the perfect pairings of four inputs.

**Definition 1.5 (Repeated pair sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.repeatedPairSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.repeatedPairSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the six terms obtained by multiplying one pair of the four coefficient functions and leaving the two other inputs separate.

**Definition 1.6 (Two pairs sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.pairPairSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.pairPairSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the three terms obtained by splitting four coefficient functions into two pairs and multiplying within each pair.

**Definition 1.7 (Triple and singleton sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.tripleSingletonSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.tripleSingletonSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the four terms obtained by choosing a singleton input and multiplying the other three coefficient functions.

**Theorem 1.8 (Expansion over ordered tuples).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment_eq_tuple_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment_eq_tuple_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A moment of weighted finite sums equals the sum over all ordered index tuples of the coefficient product times the linear functional of the corresponding algebra product.

**Theorem 1.9 (Permutation of injective tuples).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.sum_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.sum_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Precomposing every ordered injective tuple with a permutation of its positions leaves the sum of any real-valued function of the tuple unchanged.

**Theorem 1.10 (Symmetry of the distinct second moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment_pair_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment_pair_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interchanging the two coefficient functions leaves the ordered distinct-index second moment unchanged, because swapping the two indices preserves injectivity and multiplication is commutative.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.distinctIndexMoment_pair_comm`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.indexSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.pairPairSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.perfectPairingSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.quadraticFamilyMoment_eq_tuple_sum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.repeatedPairSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.sum_perm`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.tripleSingletonSum`
