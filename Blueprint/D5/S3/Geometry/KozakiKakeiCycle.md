# Recovering the cycle from its two matchings

## Abstract

The two unordered matchings partition the edges of the cycle on the columns.

**Definition 1.1 (Cyclic successor).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.step`

*Formalization.* `D5/S3/Geometry/KozakiKakeiCycle.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor adds one modulo 2m.

**Definition 1.2 (Cycle adjacency).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.Adjacent`

*Formalization.* `D5/S3/Geometry/KozakiKakeiCycle.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two columns are adjacent when either is the successor of the other.

**Definition 1.3 (Membership in a matching edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.SameEdge`

*Formalization.* `D5/S3/Geometry/KozakiKakeiCycle.SameEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two columns form an edge of the given matching in one of its two orders.

**Theorem 1.4 (Successor index).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.step_val`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.step_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value of the successor is the remainder of the index plus one modulo 2m.

**Theorem 1.5 (Successor is distinct).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.step_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.step_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cycle has at least four columns, so its successor has no fixed point.

**Theorem 1.6 (Adjacent vertices are distinct).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.adjacent_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.adjacent_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both orientations of adjacency relate distinct columns.

**Theorem 1.7 (Orientation of odd edges).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.odd_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.odd_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second end of every odd matching edge is the successor of its first end.

**Theorem 1.8 (Orientation of interior even edges).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.even_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.even_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second end of each nonclosing even edge is the successor of its first end.

**Theorem 1.9 (Orientation of the closing edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.even_closing`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.even_closing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first end of the closing even edge is the successor of its second end.

**Theorem 1.10 (Recognizing a matching edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.sameEdge_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.sameEdge_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct columns, their inverse images under the matching have the same edge index exactly when they form a matching edge.

**Theorem 1.11 (Cycle edge coverage).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.edges_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.edges_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unordered pair of distinct columns is adjacent exactly when it belongs to the odd or even matching.

**Theorem 1.12 (Disjoint cycle matchings).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.edges_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.edges_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unordered pair of distinct columns cannot be an edge of both matchings.

**Theorem 1.13 (Exact cycle reconstruction).**

Lean statement: `D5/S3/Geometry/KozakiKakeiCycle.dihedral_of_preserves_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.dihedral_of_preserves_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The images of zero and one select a start and an orientation. Injectivity forces each successive image to use the neighbor different from the preceding image. This determines a rotation or a reflection on the complete cycle.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.Adjacent`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.SameEdge`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.adjacent_ne`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.dihedral_of_preserves_adjacency`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.edges_cover`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.edges_disjoint`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.even_closing`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.even_forward`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.odd_forward`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.sameEdge_iff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.step`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.step_ne`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiCycle.step_val`
- Dependency: [D5/S3/Geometry/KozakiKakeiMatching](KozakiKakeiMatching.md)
