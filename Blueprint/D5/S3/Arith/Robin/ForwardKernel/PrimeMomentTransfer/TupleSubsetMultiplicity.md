# Tuple subset multiplicities

## Abstract

Finite box tuples containing a prescribed set have controlled multiplicity.

The estimates are repository-derived finite counting arguments. Choosing one position for each prescribed distinct value leaves all other coordinates free. The resulting estimate applies to every subfamily of a box.

**Theorem 1.1 (Prescribed values in a tuple range).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.tuple_range_superset_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.tuple_range_superset_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate type of cardinality k and a nonempty value type, a finite box S of cardinality K, and a finite prescribed value set R of cardinality r, the number of functions into S whose range contains R is at most k to the power r times K to the power k minus r. An injective choice of positions for R fixes r coordinates. A nonempty fiber embeds into the record extensions of one of its members, with values in S; RecordExtensionCount.record_extension_card bounds its cardinality by K to the power k minus r. An empty fiber satisfies the same bound.

**Theorem 1.2 (Nonnegative errors summed over tuple subsets).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.sum_tuple_subsets_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.sum_tuple_subsets_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at most four, a finite natural-number box S, any subfamily T of its k-tuples, and any nonnegative function e on finite sets, the sum over d in T and R contained in the range of d of e(R) is at most 256 times the sum over r from zero through k of K to the power k minus r times the sum of e(R) over the r-element subsets of S. This follows by interchanging the two finite sums, applying the range-containment count to each fiber, and using k to the power r at most 256.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.sum_tuple_subsets_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity.tuple_range_superset_card_le`
- Dependency: [D5/S0/Diagonal/RecordExtensionCount](../../../../../S0/Diagonal/RecordExtensionCount.md)
