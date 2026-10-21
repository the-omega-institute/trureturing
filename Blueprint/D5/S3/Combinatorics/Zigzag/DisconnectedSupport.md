# The Actual Disconnection Criterion

## Abstract

Disconnection of a balanced native choice is equivalent to actual activity of both roots and a root-separating edge coloring.

**Definition 1.1 (A count of original choices).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.disconnectedCount`

*Formalization.* `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.disconnectedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite count filters native Choices by Balanced and failure of ActiveConnected. It counts labelled choices, with unused vertices omitted from connectivity and without identifying any choices by a symmetry.

**Theorem 1.2 (Both roots must be active).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.actual_disconnected_iff_coloring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.actual_disconnected_iff_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every parameter t at least two and every balanced native choice, failure of active connectivity holds exactly when both roots are active and a Boolean coloring takes distinct prescribed values at those roots while remaining equal across every chosen edge. Actual rootedness makes every active component meet a used root. The coloring is constant on the equivalence closure of selected edges, so its distinct root values separate those components.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.actual_disconnected_iff_coloring`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DisconnectedSupport.disconnectedCount`
- Dependency: [D5/S3/Combinatorics/Zigzag/ActiveSupport](ActiveSupport.md)
