# Graph

## Abstract

Original labelled roots are computed from unique paths in actual star spanning trees for the wheel and K4 seed.

**Definition 1.1 (wheelGraphData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual hub-star/rim-interface wheel. The marked e is rim edge 1--2, not a spoke or a coordinate of this right tree.

**Theorem 1.2 (fundamental_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.fundamental_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Graph.fundamental_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These are path-derived rows, not an input equation.

**Theorem 1.3 (wheelOriginalRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelOriginalRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelOriginalRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting the ACTUAL interface chord row gives E; the full root is A1.

**Definition 1.4 (wheelGraphCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native supplier certificates consume this actual graph-derived root.

**Definition 1.5 (seedGraphData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native supplier certificates consume this actual graph-derived root.

**Theorem 1.6 (seedOriginalRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedOriginalRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedOriginalRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K4's actual star-tree paths compute the seed row root.

**Definition 1.7 (seedGraphCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K4's actual star-tree paths compute the seed row root.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.fundamental_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedGraphData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.seedOriginalRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelGraphData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Graph.wheelOriginalRoot`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore](GraphDataCore.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Wheel](Wheel.md)
