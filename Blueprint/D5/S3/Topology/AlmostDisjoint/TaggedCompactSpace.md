# Coherent tags produce a compact open surjection

## Abstract

The literal tagged compact product and its open projection.

A is a set of distinct actual subsets of Nat whose distinct members have finite intersections; infinity of each member is not required for this construction. Its subtype, rather than repeated branch labels, supplies the family coordinates. The ambient space is OnePoint Nat times unitInterval times Bool^(A + Nat). The literal space retains the entire zero-vector interval core, the actual d_n with all membership and singleton coordinates, every finite nonmember family tag and the tagged limit point for every actual member.

The information audit remains unfinished: the source-owner mirror checks the exact generic source telescope. A faithful whole-source variation arena and raw source occurrence reconstruction/sourceSelection remain absent; the same-target issue is linked in the final delivery. This is not a validated four-slot registration.

**Theorem 1.1 (Closed coordinate shell, continuous sections and clopen section ranges).**

$$\forall A: \operatorname{Set}\left(\operatorname{Set}\left(Nat\right)\right), \forall u: Nat \to unitInterval, \forall ell: A \to unitInterval, \operatorname{PairwiseFiniteIntersections}\left(A\right) \land {\forall a: A, \operatorname{ConvergesOn}\left(u, \operatorname{val}\left(a\right), \operatorname{ell}\left(a\right)\right)} \Rightarrow \operatorname{IsClosed}\left(\operatorname{literalSpace}\left(A, u, ell\right)\right) \land \operatorname{IsCompact}\left(\operatorname{literalSpace}\left(A, u, ell\right)\right) \land \operatorname{Continuous}\left(\operatorname{projection}\left(A, u, ell\right)\right) \land \operatorname{IsOpenMap}\left(\operatorname{projection}\left(A, u, ell\right)\right) \land \operatorname{Surjective}\left(\operatorname{projection}\left(A, u, ell\right)\right) \land {\forall a: A, \operatorname{Continuous}\left(\operatorname{sectionLift}\left(A, u, ell, a\right)\right)} \land {\forall a: A, \operatorname{IsClopen}\left(\operatorname{range}\left(\operatorname{sectionLift}\left(A, u, ell, a\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace.literal_closed_compact_open_surjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a in A, its section agrees with d_n when n lies in a, and otherwise uses its own tagged point at the base n. The value coordinate converges by the assumed finite-exception convergence on a. Almost-disjoint intersections and singleton coordinates make every other tag coordinate eventually constant. The section is continuous into the actual product.

Each family coordinate piece is a continuous compact section range; each natural-number coordinate piece is a singleton. If any tag is true at a point in one coordinate piece, that point belongs to the corresponding piece. Consequently the literal union is exactly the intersection, over every coordinate gamma, of the closed false-coordinate slice union its compact coordinate piece. This uses arbitrary closed intersections and does not assume countability, sequentiality, CH or regularity of continuum.

At infinity every point lies on a continuous core or family section. At a finite isolated base point, overwrite a core section to pass through the selected fiber point. Mathlib IsOpenMap.of_sections proves that the actual projection is open. The core also proves it is onto. Each family section range equals its own true-coordinate slice and is clopen.

The result works for an arbitrary actual family with pairwise finite intersections with the stated convergence, including an empty family, and exposes the natural points, sections and projection for the subsequent closed-piece partitioner argument. It does not by itself prove the finite-refinement obstruction, the base classification or the original Peng dynamical question.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/TaggedCompactSpace.literal_closed_compact_open_surjection`
- Dependency: [D5/S3/Topology/AlmostDisjoint/ConvergentBranches](ConvergentBranches.md)
