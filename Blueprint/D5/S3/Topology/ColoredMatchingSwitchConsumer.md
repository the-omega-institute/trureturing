# Circle changes at an actual weaving crossing

## Abstract

Circle changes at an actual weaving crossing.

Let P have n at least two and m at least three, let p be either parity, and let S be any finite crossing subset. Insert a crossing z outside S. The four actual ports at z are pairwise distinct, and the new mixed matching agrees with the old one away from these ports.

**Theorem 1.1 (Circle changes at an actual weaving crossing).**

Lean statement: `D5/S3/Topology/ColoredMatchingSwitchConsumer.mixed_insert_circle_count`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ColoredMatchingSwitchConsumer.mixed_insert_circle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic colored matching surgery gives an absolute integer circle-count change at most one. If the two reference endpoint components at z are distinct in the spanning graph on S, the descended mixed-component map puts the two old local arcs in distinct mixed circles; the insertion therefore reduces the circle count by exactly one. No rank formula or global arbitrary-state circle identity is assumed. The result applies to empty, disconnected and almost-full states, and includes the cyclic closing seam.

These finite matching statements are auxiliary to weaving coefficient asymptotics. They do not identify a state polynomial with the source trace-defined Jones invariant or establish the original twist-number limit.

## References

- Truth anchor: `D5/S3/Topology/ColoredMatchingSwitchConsumer.mixed_insert_circle_count`
- Dependency: [D5/S3/Topology/ColoredMatchingSwitch](ColoredMatchingSwitch.md)
- Dependency: [D5/S3/Topology/WeavingMixedComponents](WeavingMixedComponents.md)
