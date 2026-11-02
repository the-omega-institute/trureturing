# Euler defect of arbitrary weaving states

## Abstract

The actual mixed-circle count equals uniform vertices plus selected crossings minus twice spanning rank.

Let P have n at least two and m at least three, let p be either smoothing parity, and let S be an arbitrary crossing subset. Write v for the number of uniform circles, c(S) for the number of actual mixed circles, and q(S) for v minus the number of connected components of the spanning reference graph on S. Every uniform circle is a graph vertex, including isolated vertices. The empty, full and disconnected states and the cyclic seam all belong to the same finite family.

**Theorem 1.1 (The exact spanning rank increment).**

Lean statement: `D5/S3/Topology/WeavingEulerDefect.q_insert_add_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingEulerDefect.q_insert_add_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one crossing increases rank by one exactly when its endpoints were in different old spanning components. The one-edge reachability classifier collapses precisely those two component classes, and preserves every other class. This proves the component-cardinality change directly on the full vertex quotient.

**Theorem 1.2 (Monotonicity of the Euler defect).**

Lean statement: `D5/S3/Topology/WeavingEulerDefect.Delta_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingEulerDefect.Delta_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define Delta(S)=v+|S|-2q(S)-c(S) in the integers. When rank increases, distinct reference components force distinct mixed circles and colored surgery merges them, so Delta is unchanged. When rank is unchanged, the universal surgery bound gives c(S union {z})-c(S) at most one, so Delta cannot decrease. Finite insertion induction yields monotonicity under arbitrary subset inclusion.

**Theorem 1.3 (The circle identity for every state).**

Lean statement: `D5/S3/Topology/WeavingEulerDefect.mixed_circle_count_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingEulerDefect.mixed_circle_count_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty defect is zero. For the full state, the reference graph is connected, full switching gives the complementary uniform smoothing, and the two uniform circle counts sum to nm+2. Its defect is therefore zero as well. Every subset lies between the empty and full subsets; monotonicity forces its defect to vanish. Consequently c(S)+2q(S)=v+|S|, without excluding zero-change switches in unrelated matching systems.

**Theorem 1.4 (The nonnegative state exponent).**

Lean statement: `D5/S3/Topology/WeavingEulerDefect.mixed_circle_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingEulerDefect.mixed_circle_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mixed quotient is nonempty. Thus v-1+|S|-2q(S)=c(S)-1 is nonnegative. This is the exponent needed to compare the graph state sum with the literal mixed-circle state sum.

These identities concern the actual combinatorial state quotients. Identification with the primary source's Jones invariant additionally requires the planar closure trace, the integral Hecke trace restriction, legitimate ring base change and the compatible localized square root. No such identity is an assumption here.

## References

- Truth anchor: `D5/S3/Topology/WeavingEulerDefect.Delta_monotone`
- Truth anchor: `D5/S3/Topology/WeavingEulerDefect.mixed_circle_count_nat`
- Truth anchor: `D5/S3/Topology/WeavingEulerDefect.mixed_circle_exponent`
- Truth anchor: `D5/S3/Topology/WeavingEulerDefect.q_insert_add_one_iff`
- Dependency: [D5/S3/Topology/ColoredMatchingSwitchConsumer](ColoredMatchingSwitchConsumer.md)
