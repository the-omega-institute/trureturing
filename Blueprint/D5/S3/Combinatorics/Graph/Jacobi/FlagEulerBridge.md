# Actual flag incidence preserves Euler genus

## Abstract

Actual flag incidence preserves Euler genus

**Definition 1.1 (Original edges retain their two actual flags).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.edgePairGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.edgePairGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge-pair graph has the original flags as vertices, and pairs precisely the two flags exchanged by the fixed-point-free involution. Its unordered edges count the original graph edges. Distinct pairs remain distinct when their rotor-orbit endpoints coincide or repeat, so original loops and parallel edges are retained.

**Definition 1.2 (Original Euler genus).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.eulerGenus`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.eulerGenus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite flags, eulerGenus is the number of original edge pairs plus one, followed by natural subtraction of the number of actual rotor orbits. On a connected graph this is its first Betti number. The exceptional bare topological circle has no flags or Jacobi vertices and remains a separate source case; it is not represented by this definition.

**Theorem 1.3 (Subdivision preserves the Euler count).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.incidence_euler_genus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.incidence_euler_genus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite cyclic flag graph, the actual incidence graph has the same edge-plus-one-minus-vertex count as the original graph. The proof identifies each orbit node's neighbors with the flags it owns and each flag node's neighbors with a two-element set: its owner orbit and its edge mate. Handshaking gives twice the incidence edge count equal to three times the flag count, while the original edge-pair graph gives twice its edge count equal to the flag count. The incidence vertex count is the sum of orbit and flag counts. Natural arithmetic then proves the exact equality, without assuming connectivity or excluding loops and parallel edges.

**Theorem 1.4 (Positive connected genus is exactly an actual cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.positive_euler_genus_iff_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.positive_euler_genus_iff_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite flag graph whose actual incidence graph is connected, original Euler genus is positive if and only if the incidence graph is not acyclic. The proof uses the exact subdivision count and Mathlib's connected tree edge-count criterion. This closes the positive-genus-versus-cycle condition needed by the existing Stable pruning predicate on the finite-flag carrier. It does not by itself compare the connected fixed-grade source quotient with the all-diagram quotient, construct a bare circle, or prove four-loop vanishing.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.edgePairGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.eulerGenus`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.incidence_euler_genus`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge.positive_euler_genus_iff_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/FlagPruning](FlagPruning.md)
