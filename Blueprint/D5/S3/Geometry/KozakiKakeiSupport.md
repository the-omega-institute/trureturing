# The signed Boolean support recovers adjacency

## Abstract

For m at least four, counting nonzero evaluations with two specified true coordinates determines whether those columns are adjacent.

**Definition 1.1 (Boolean evaluation coordinates).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.boolNumber`

*Formalization.* `D5/S3/Geometry/KozakiKakeiSupport.boolNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

False maps to zero and true maps to one in the complex field.

**Definition 1.2 (Matching transversals).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.Cuts`

*Formalization.* `D5/S3/Geometry/KozakiKakeiSupport.Cuts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean assignment cuts a matching when the two values on every edge differ.

**Theorem 1.3 (Nonzero matching evaluations).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.eval_matching_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiSupport.eval_matching_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An oriented matching polynomial is nonzero on a Boolean assignment exactly when the assignment cuts every matching edge.

**Theorem 1.4 (Forcing the two endpoints).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.cuts_separate`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiSupport.cuts_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an assignment cuts a matching and the two columns lie on the same edge, their assigned values differ.

**Theorem 1.5 (Signed support counts detect edges).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.signed_support_recovers_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiSupport.signed_support_recovers_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an adjacent pair, one matching admits no cuts with both entries true and the other has exactly 2 to the power m−2. For a nonedge both matchings have that many cuts, with at most one common cut. Removing all possible common cancellations leaves strictly more than the edge count when m is at least four.

**Theorem 1.6 (Scalar symmetry transports support counts).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.pairSupport_card_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiSupport.pairSupport_card_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composition of Boolean assignments with the permutation bijects the two supports. The nonzero scalar preserves the property of evaluating to a nonzero value.

**Theorem 1.7 (Large-order necessity).**

Lean statement: `D5/S3/Geometry/KozakiKakeiSupport.dihedral_of_scalar_large`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiSupport.dihedral_of_scalar_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar symmetry preserves adjacency by the support count, and the cycle reconstruction forces the relabeling to be dihedral.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.Cuts`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.boolNumber`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.cuts_separate`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.dihedral_of_scalar_large`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.eval_matching_ne_zero`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.pairSupport_card_invariant`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiSupport.signed_support_recovers_adjacency`
- Dependency: [D5/S3/Geometry/KozakiKakeiConstantBridge](KozakiKakeiConstantBridge.md)
- Dependency: [D5/S3/Geometry/KozakiKakeiCycle](KozakiKakeiCycle.md)
