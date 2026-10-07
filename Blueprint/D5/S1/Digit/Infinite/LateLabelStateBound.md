# Late nonnull labels at finite-source extrema

## Abstract

Late nonnull labels at finite-source extrema.

**Definition 1.1 (Finite full-path representations).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.Representation`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.Representation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite directed multigraph has finite vertex and edge types, an incoming Boolean guard at each vertex, and an original legal three-bit label at each edge. Each edge obeys the original guard transition. All vertices in the finite initial set have guard zero. Parallel edges and nondeterministic choices are permitted.

**Definition 1.2 (All infinite paths).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.Path`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path is any infinite sequence of edges whose successive target and source vertices agree. No further acceptance condition or scalar membership test is imposed.

**Definition 1.3 (Actual edge deletion).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.shiftPath`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.shiftPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Deleting n edges of a path deletes exactly n original three-bit windows.

**Definition 1.4 (Replacement of a continuation).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.splicePath`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.splicePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any infinite continuation starting at the vertex reached after n edges can replace the tail of a path, with all preceding edges retained.

**Definition 1.5 (Actual source addresses).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.pathAddress`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.pathAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenating the original three-bit edge labels gives a legal infinite Boolean address. The edge guards prevent adjacent ones across window boundaries. Its scalar is the original window series kappa, with no initial offset.

**Definition 1.6 (The total initial scalar image).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.scalarImage`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.scalarImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total image consists of the original scalar values of all infinite paths whose first vertex belongs to the initial set.

**Definition 1.7 (Surviving vertices).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.Surviving`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.Surviving` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex survives precisely when some infinite compatible path starts there. Vertices that are unreachable from the initial set are allowed to survive.

**Definition 1.8 (Surviving vertex count).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.survivorCount`

*Formalization.* `D5/S1/Digit/Infinite/LateLabelStateBound.survivorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The number s is the finite cardinality of the surviving vertex type.

**Theorem 1.9 (The late-label lower bound).**

Lean statement: `D5/S1/Digit/Infinite/LateLabelStateBound.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/LateLabelStateBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such finite representation, every minimum or maximum e of its total initial scalar image, every actual eventually-zero address x with kappa(x)=e, and every zero-based window position j with a nonnull label, the surviving vertex count satisfies s>=ceil((j+2)/2).

The signed golden-series fiber classification implies that an eventually-zero address is the only legal address over its scalar. The two addresses at each seam have nonzero alternating tails, even after a finite prefix.

Replacing a path tail after n windows changes the scalar by (-g)^n times the change of tail scalar. At two occurrences of the same vertex with the same parity, extremality in both replacement directions forces the tail scalars to agree. The finite-source uniqueness then forces the whole tail addresses to agree.

Equal tails at two distinct positions are periodic from the earlier position onward. An eventually-zero tail with a positive period is entirely zero. A nonnull window at j therefore forces the first j+2 signed vertices to be distinct. Each signed vertex consists of one surviving vertex and a parity, so there are only 2s available states.

## References

- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.Path`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.Representation`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.Surviving`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.pathAddress`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.result`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.scalarImage`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.shiftPath`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.splicePath`
- Truth anchor: `D5/S1/Digit/Infinite/LateLabelStateBound.survivorCount`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
