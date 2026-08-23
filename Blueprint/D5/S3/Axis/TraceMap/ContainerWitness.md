# Container Witness

## Abstract

One statement naming the parent receipt's carrier and the whole child package.

The container atom carries a pre-committed receipt naming one carrier, while its three clause atoms are covered by declarations written eight days later under a different index convention. Covering the parent against a carrier its children do not use would certify an equivalence nobody had proved.

This statement names both sides at once: the recurrence pair the parent's own carrier proves at the substituted readings, the coherence relation carrying that carrier onto the one the children use, and the child recurrence itself. Each conjunct is an existing theorem applied; none is restated.

What the conjunction adds is that they hold of one pair of readings at once. Removing the substitution from the parent conjunct makes the module fail to build, so the three blocks are bound together rather than merely adjacent.

**Theorem 1.1 (The parent carrier and the child package together).**

$$\operatorname{tracePartial}\left(K + 2\right) = \operatorname{tracePartial}\left(K + 1\right) + \operatorname{tA}\left(K + 2\right) \cdot \operatorname{tracePartial}\left(K\right) \land \left(\operatorname{tracePartial}\left(J\right) = \operatorname{axisPartialSum}\left(J + 1\right) \land \operatorname{axisPartialSum}\left(J + 2\right) = \operatorname{axisPartialSum}\left(J + 1\right) + \operatorname{tB}\left(J + 2\right) \cdot \operatorname{axisPartialSum}\left(J\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/ContainerWitness.container_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A necessary condition for settling the container, not a sufficient one: which index convention the source text intends remains unmeasured, and that is what would decide whether either carrier is faithful to it.

## References

- Truth anchor: `D5/S3/Axis/TraceMap/ContainerWitness.container_witness`
- Dependency: [D5/S3/Axis/TraceMap/CarrierCoherence](CarrierCoherence.md)
- Dependency: [D5/S3/Axis/TraceMap/Theorem635](Theorem635.md)
