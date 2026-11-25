# Pendant arcs obstruct finite positive expansivity of exact maps

## Abstract

Pendant arcs obstruct finite positive expansivity of exact maps

A pendant arc is an embedded closed interval whose image with the attachment endpoint removed is open in the carrier. Topological exactness means that some positive iterate of each nonempty open set covers the carrier.

**Theorem 1.1 (Arbitrarily large families coalesce at every positive scale).**

Lean statement: `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.coalescing_witnesses`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.coalescing_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a compact metric space contain a pendant arc, and let its continuous selfmap be topologically exact. For every positive radius and finite cardinality there is an injectively indexed family whose orbits are pairwise strictly closer than that radius at all forward times. All points in the family have a common image at one finite time.

Exactness makes an iterate reach the leaf from the interior of any pendant subarc. With finite fibers, the two sides of a preimage of the leaf both map over a common smaller subarc. Shrink the source to control the finite orbit prefix, then lift the inductive family through both sides. An infinite fiber already supplies arbitrarily large families in one small ball.

**Theorem 1.2 (Exact dynamics excludes finite positive expansivity on a pendant arc carrier).**

Lean statement: `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.not_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.not_finitelyPositiveExpansive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous topologically exact selfmap of a compact metric space with a pendant arc, the coalescing families rule out every finite uniform bound on strict forward Bowen sets. A finite graph with a leaf has such an arc.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.coalescing_witnesses`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ExactPendantObstruction.not_finitelyPositiveExpansive`
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic](IntervalObstruction/Basic.md)
