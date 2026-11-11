# Pairing partition correspondence

## Abstract

The bijection between retained singleton/free pair partitions and unordered partial pairings.

For any natural k, a partition of the positions Fin k is a Mathlib Setoid, and its blocks are quotient classes. The block sizes use the existing multiplicity function mult from ArithmeticTransferDefs. The degree-zero collision shape consists of retained singleton blocks and unretained two-element blocks. No ordering of the blocks or of their labels is chosen.

**Definition 1.1 (Labels of a quotient block).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a setoid sigma on Fin k and a quotient block B, partitionLabelBlock(sigma,B) is the finite set of positions i whose quotient class equals B. Its cardinality is definitionally mult(Quotient.mk(sigma),B).

**Theorem 1.2 (Distinct blocks have distinct fibers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and setoid sigma on Fin k, the map B to partitionLabelBlock(sigma,B) is injective. Each block contains its quotient representative; equality of fibers forces equality of the quotient classes.

**Definition 1.3 (Retained singleton/free pair data).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.PairingPartitionData`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.PairingPartitionData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PairingPartitionData(k) consists of a setoid sigma on Fin k, a finite set S of its retained quotient blocks, and the laws mult(Quotient.mk(sigma),B)=1 for B in S and =2 for B outside S.

**Definition 1.4 (The free blocks as pairs).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For degree-zero partition data D, pairingPartitionPairs(D) is the image of the complement of its retained set under the label-fiber map. It is a finite set of unordered two-element label sets.

**Theorem 1.5 (The resulting collection is a partial pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_isPartial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_isPartial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and D in PairingPartitionData(k), pairingPartitionPairs(D) satisfies IsPartialPairing on all positions Fin k. Every unretained fiber has size two and distinct quotient fibers are disjoint.

**Theorem 1.6 (Covered and retained labels).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and degree-zero partition data D, the support of pairingPartitionPairs(D) equals the positions i whose quotient block is not retained. Thus its uncovered labels are exactly the labels in retained singleton blocks.

**Theorem 1.7 (Cardinality-preserving bijection with partial pairings).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the map from PairingPartitionData(k) to the subtype of partial pairings of Fin k, sending D to pairingPartitionPairs(D) together with its partial-pairing proof, is bijective. For every D, the number of resulting pairs equals the number of unretained quotient blocks. The original partition relation is recovered by saying that two labels are equal or lie together in one of the free pairs. The retained blocks are then determined by their singleton sizes, proving injectivity. Conversely, for any partial pairing P, use this equality-or-common-edge relation as a setoid. Disjointness of the edges proves transitivity. A covered label has its edge as quotient fiber; an uncovered label has a singleton fiber. Retaining exactly the singleton fibers constructs inverse partition data whose free pairs are precisely P. The construction also includes the empty label type and the empty partial pairing.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.PairingPartitionData`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_bijective`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_isPartial`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.pairingPartitionPairs_support`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.partitionLabelBlock_injective`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial](PartialPairingPolynomial.md)
