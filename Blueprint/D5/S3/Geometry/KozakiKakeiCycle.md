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

$$\forall m : \mathbb{N}, \forall i : \operatorname{Col}(m), 2 \le m \implies \operatorname{val}(\operatorname{step}(i)) = (\operatorname{val}(i)+1) \operatorname{mod} (2 \cdot m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.step_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value of the successor is the remainder of the index plus one modulo 2m.

**Theorem 1.5 (Successor is distinct).**

$$\forall m : \mathbb{N}, \forall i : \operatorname{Col}(m), 2 \le m \implies \operatorname{step}(i) \neq i$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.step_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cycle has at least four columns, so its successor has no fixed point.

**Theorem 1.6 (Adjacent vertices are distinct).**

$$\forall m : \mathbb{N}, \forall i,j : \operatorname{Col}(m), 2 \le m \implies \operatorname{Adjacent}(i,j) \implies i \neq j$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.adjacent_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both orientations of adjacency relate distinct columns.

**Theorem 1.7 (Orientation of odd edges).**

$$\forall m : \mathbb{N}, \forall e : \operatorname{Fin}(m), 2 \le m \implies \operatorname{step}(\operatorname{oddVertex}(e,\operatorname{false})) = \operatorname{oddVertex}(e,\operatorname{true})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.odd_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second end of every odd matching edge is the successor of its first end.

**Theorem 1.8 (Orientation of interior even edges).**

$$\forall m : \mathbb{N}, \forall e : \operatorname{Fin}(m), 2 \le m \implies \operatorname{val}(e) \neq 0 \implies \operatorname{step}(\operatorname{evenVertex}(e,\operatorname{false})) = \operatorname{evenVertex}(e,\operatorname{true})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.even_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second end of each nonclosing even edge is the successor of its first end.

**Theorem 1.9 (Orientation of the closing edge).**

$$\forall m : \mathbb{N}, \forall e : \operatorname{Fin}(m), 2 \le m \implies \operatorname{val}(e) = 0 \implies \operatorname{step}(\operatorname{evenVertex}(e,\operatorname{true})) = \operatorname{evenVertex}(e,\operatorname{false})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.even_closing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first end of the closing even edge is the successor of its second end.

**Theorem 1.10 (Recognizing a matching edge).**

$$\forall m : \mathbb{N}, \forall M : \operatorname{Matching}(m), i,j : \operatorname{Col}(m), i \neq j \implies (\operatorname{SameEdge}(M,i,j) \iff (\exists e : \operatorname{Fin}(m), (i=M(e,\operatorname{false}) \land j=M(e,\operatorname{true})) \lor (i=M(e,\operatorname{true}) \land j=M(e,\operatorname{false}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.sameEdge_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct columns, their inverse images under the matching have the same edge index exactly when they form a matching edge.

**Theorem 1.11 (Cycle edge coverage).**

$$\forall m : \mathbb{N}, \forall i,j : \operatorname{Col}(m), 2 \le m \implies i \neq j \implies (\operatorname{Adjacent}(i,j) \iff (\operatorname{SameEdge}(\operatorname{oddMatching}(m),i,j) \lor \operatorname{SameEdge}(\operatorname{evenMatching}(m),i,j)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.edges_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unordered pair of distinct columns is adjacent exactly when it belongs to the odd or even matching.

**Theorem 1.12 (Disjoint cycle matchings).**

$$\forall m : \mathbb{N}, \forall i,j : \operatorname{Col}(m), 2 \le m \implies i \neq j \implies \operatorname{SameEdge}(\operatorname{oddMatching}(m),i,j) \implies \neg\operatorname{SameEdge}(\operatorname{evenMatching}(m),i,j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiCycle.edges_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An unordered pair of distinct columns cannot be an edge of both matchings.

**Theorem 1.13 (Exact cycle reconstruction).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies (\forall i,j : \operatorname{Col}(m), \operatorname{Adjacent}(i,j) \implies \operatorname{Adjacent}(s(i),s(j))) \implies \operatorname{Dihedral}(s)$$

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
