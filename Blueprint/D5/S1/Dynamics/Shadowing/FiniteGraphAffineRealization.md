# Affine realization of a finite simple graph

## Abstract

Affine realization of a finite simple graph

**Theorem 1.1 (Distance between incident edge germs).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.dist_edgeChart_incident`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.dist_edgeChart_incident` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a shared vertex, the sup distance between points on two different edges is the maximum of their parameters measured from that vertex. The two distinct endpoint coordinates attain the required lower bounds.

**Theorem 1.2 (The tip of a leaf edge is open).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.tip_eq_pos_coord`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.tip_eq_pos_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive leaf coordinate singles out the part of the unique incident edge away from its attachment. This yields the pendant arc used in the obstruction.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.dist_edgeChart_incident`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.tip_eq_pos_coord`
- Dependency: [D5/S1/Dynamics/Shadowing/ExactPendantObstruction](ExactPendantObstruction.md)
