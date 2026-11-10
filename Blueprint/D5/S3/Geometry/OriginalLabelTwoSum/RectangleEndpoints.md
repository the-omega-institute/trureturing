# RectangleEndpoints

## Abstract

Raw cuts of the two descending rectangles equal the exact changed Phi states.

**Theorem 1.1 (deletionCut).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionCut`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact deletion-rectangle endpoint, including every empty-fibre case. 

**Theorem 1.2 (linkCut).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkCut`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact link-rectangle endpoint. L<=D accounts for the fibres already retained in D*delta(Z); an empty projected lower is handled without an ordinary move. 

**Definition 1.3 (deletionLift).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionLift`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Endpoint-transported deletion rule consumes its proved raw equality. 

**Definition 1.4 (linkLift).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkLift`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Endpoint-transported link rule consumes its proved raw equality. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionCut`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.deletionLift`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkCut`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints.linkLift`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Rectangles](Rectangles.md)
