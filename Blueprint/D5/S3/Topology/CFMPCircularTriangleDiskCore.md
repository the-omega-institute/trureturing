# Core invariants of a cyclic triangle fan

## Abstract

The cyclic triangle-fan seam relation preserves radial size and joins all labelled origins.

A triangle is a pair of nonnegative real coordinates with sum at most one. The finite fan has one copy of this triangle for each label in `Fin(n)`, with `0 < n`. The seam relation is the reflexive, symmetric and transitive closure of the actual edge generators. This document records the radial invariant and the zero-radius fibre needed by the later quotient-disk construction. It does not assert the complex angular map, quotient Hausdorffness, or the final homeomorphism.

**Theorem 1.1 (Radial size is constant on generated seam classes).**

$$\forall n \in Nat,\; \forall hn \in (0 < n),\; \forall x,y \in Fan(n),\; SeamRel(n,hn,x,y) \Rightarrow radialSize(x)=radialSize(y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CFMPCircularTriangleDiskCore.radialSize_eq_of_seamRel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each generating seam keeps the same edge parameter, hence the same sum of triangle coordinates. The equality propagates through the three constructors of `Relation.EqvGen`. This is the invariant required for a radial representative map to descend to the quotient.

**Theorem 1.2 (A generator joins consecutive labelled origins).**

$$\forall n \in Nat,\; \forall hn \in (0 < n),\; \forall i \in Fin(n),\; SeamRel(n,hn,originEdge(i),originEdge(next(hn,i)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.* The parameter `t=0` is an actual seam generator. The relation is defined by these seams and never by the kernel of a candidate radial map.

**Theorem 1.3 (All labelled origins lie in one generated class).**

$$\forall n \in Nat,\; \forall hn \in (0 < n),\; \forall i \in Fin(n),\; SeamRel(n,hn,originEdge(0),originEdge(i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.* Finite induction follows the explicit modulo successor and joins every origin to the origin in copy zero.

**Theorem 1.4 (Every labelled origin has radial size zero).**

$$\forall n \in Nat,\; \forall hn \in (0 < n),\; \forall i \in Fin(n),\; radialSize(originEdge(i))=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_radial_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.* Together with the preceding two statements, this identifies the distinguished zero-radius class. The remaining clauses of the source theorem—complex angular coordinates, exact fibres away from zero, quotient compactness and the homeomorphism—remain open.

## References

- Truth anchor: `D5/S3/Topology/CFMPCircularTriangleDiskCore.radialSize_eq_of_seamRel`
- Truth anchor: `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_step`
- Truth anchor: `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_all`
- Truth anchor: `D5/S3/Topology/CFMPCircularTriangleDiskCore.seam_origin_radial_zero`
