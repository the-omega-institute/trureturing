# Private Pairs in Omission Families

## Abstract

Private elements and the intersections of omitted sets.

**Definition 1.1 (Private pairs).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.HasPrivatePairs`

*Formalization.* `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.HasPrivatePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every member of a finite family of finite sets contains two distinct elements that belong to no other member.

**Theorem 1.2 (Restriction to a subfamily).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any subfamily inherits the two private elements of each of its members.

**Theorem 1.3 (Pairs in disjoint petals).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.of_disjoint_petals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.of_disjoint_petals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If erasing a fixed element leaves pairwise disjoint sets of size at least two, two elements from each erased set give private pairs for the original family.

**Theorem 1.4 (Intersection bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.inter_card_add_two_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.inter_card_add_two_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The intersection of two distinct members, together with two private elements of the first, lies inside the first member. Thus the intersection has at most the first member's cardinality minus two elements.

**Theorem 1.5 (Erasing a common element).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.erase_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.erase_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume each member has a private pair, the fixed element belongs to every member, and each erased set has size at least two. Every erased set admits two private elements. For a family of at least two members the original private elements survive erasure. For one member any two remaining elements suffice.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.HasPrivatePairs`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.erase_exists`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.inter_card_add_two_le`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.mono`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily.of_disjoint_petals`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitWeightBlocks](CircuitWeightBlocks.md)
