# Entire row and column vectors on one realization

## Abstract

Joint indexed reconstruction on actual residual arrays.

**Definition 1.1 (Both cumulative coordinates of every extremum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.JointExtremaExpansion`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.JointExtremaExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each actual expanded cell, strict minimum status is equivalent to coming from an original strict minimum with both coordinates equal to the corresponding cumulative insertion coordinates. The equivalence is also imposed separately for maxima. Every original cell and every full physical neighbour remains interpreted on its actual rectangle.

**Theorem 1.2 (Simultaneous realization of both complete vectors).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an actual residual array with both dimensions at least two, prescribe natural extra-copy coordinates at every original row and column, supported on genuinely frozen lines on the corresponding axis. One actual normalized unit-edge array exists at dimensions m plus the row-vector sum and n plus the column-vector sum. It retains the exact residual split and common-side exclusion, reduces to the original array by legal joint deletions, and transports every individual minimum and maximum to both prescribed cumulative coordinates. Column expansion preserves occupied original rows; the actual inactive-row criterion then makes all prescribed row insertions available in the same realization.

**Theorem 1.3 (Read back every coordinate on both axes).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_weights_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_weights_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an actual unit-edge core with both dimensions at least two and no adjacent frozen pair on either axis. If two supported row vectors and two supported column vectors have the same corresponding output dimensions and the same actual output function satisfies both joint extremum expansions, the entire row vectors agree and the entire column vectors agree. The exact occupied images are read from that one output and the one-axis readback theorem is applied to both physical axes. No choice-independent canonical-core theorem and no fiber cardinality are assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.JointExtremaExpansion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_expansion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberJoint.indexed_joint_weights_unique`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreJoint](MiuraCoreJoint.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreTranspose](MiuraCoreTranspose.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberIndexed](MiuraFiberIndexed.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberReadback](MiuraFiberReadback.md)
