# Omitted Sets Distinguished by Membership

## Abstract

Omissions with pairwise separation by nonsingleton membership classes.

**Definition 1.1 (Distinguishing membership classes).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.HasSeparatedMembership`

*Formalization.* `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.HasSeparatedMembership` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair of distinct omitted sets differs on some class containing at least two distinct indices. Indices in one class belong to exactly the same omitted sets.

**Theorem 1.2 (Passage to a subfamily).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair of indices in one membership class still has the same membership after restricting to a subfamily. A class distinguishing two retained sets still distinguishes them.

**Theorem 1.3 (Pairwise intersection bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.inter_card_add_two_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.inter_card_add_two_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct members of equal cardinality share at most their size minus two indices. The distinguishing class contributes two indices to the difference in one direction. Equal cardinality gives the same bound in either direction.

**Theorem 1.4 (Private pairs give separation).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.of_private_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.of_private_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A private pair belongs only to its own omitted set. It therefore gives two indices with the same membership and distinguishes that set from any other.

**Theorem 1.5 (Two bounds for the number of omissions).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.omission_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.omission_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider r-element omissions with a common element in a K-element set. Suppose distinct omissions intersect in at most r minus two elements. Removing the common element, then deleting an index while avoiding one fixed coordinate, injects the petals into the (r minus two)-element subsets of the remaining K minus two indices. Complementing the petals gives the other bound. Thus the family has at most binom(K minus 2, r minus 2) and binom(K minus 2, r minus 1) members.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.HasSeparatedMembership`
- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.inter_card_add_two_le`
- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.mono`
- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.of_private_pairs`
- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions.omission_multiplicities`
