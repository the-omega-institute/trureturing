# Switches in Point-Deleted Steiner Systems

## Abstract

Deleting a point from a complete Steiner system leaves a matching. A path replacement controls the first deficit.

**Definition 1.1 (The retained packing).**

Lean statement: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.pointDeletedFamily`

*Formalization.* `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.pointDeletedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep exactly the original blocks avoiding the distinguished point, using the complementary embedding to label the remaining points.

**Definition 1.2 (The two-block switch).**

Lean statement: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.switchedPacking`

*Formalization.* `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.switchedPacking` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the path in order a,b,v,d,c remove the blocks abv and vdc, then add avc.

**Definition 1.3 (The matching and path in the leave).**

Lean statement: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.SwitchedLeave`

*Formalization.* `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.SwitchedLeave` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the matching edges away from the two path endpoints, and include exactly the four successive path edges.

**Theorem 1.4 (Maximality after a point-deleted switch).**

Lean statement: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.point_deleted_switch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.point_deleted_switch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complete Steiner triple system and any distinguished point, the retained packing has exactly a fixed-point-free involution m as its leave. For any a and v with v distinct from a and m(a), put c=m(a). The retained pairs av and cv have completions b and d.

The switched family keeps pair uniqueness and has one fewer block. Its leave replaces ac by the path a,b,v,d,c. The remaining matching has at most one edge between any vertex and the rest. A triangle must therefore use two successive path edges. Only the two interior vertices b and d can be joined by a remaining matching edge, because a and c were paired to each other. The switch is maximal exactly when d is not m(b).

**Theorem 1.5 (One fewer block than the largest saturated extension).**

Lean statement: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.matching_switch_first_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.matching_switch_first_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive row dimension, and fix the lifted cross-row family with distinct rows, pair uniqueness and zero-sum completion of every cross-row pair. As in the classwise decomposition, normalize at zero and preserve dimension one more than the row dimension. Suppose the residue labels have a packing whose leave is a perfect matching, together with two blocks giving a successful switch of the described shape.

In that packing each label has exactly one unused partner and every block through a label uses two partners. Thus the label count r is even. Every other packing has at least one unused partner at every label, so the matching packing attains the upper bound r(r−2)/6. This count times the number of actual residue classes, plus the rowwise Latin cells, bounds every compatible extension. A saturated extension attains that bound. A successful switch in one class realizes one fewer.

For the classical local spectrum see Colbourn, Rosa and Znám (https://doi.org/10.1007/BF01388482). The criterion here concerns the specified local switch on the input system and its effect on the dimension-preserving extension.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.SwitchedLeave`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.matching_switch_first_deficit`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.pointDeletedFamily`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.point_deleted_switch`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch.switchedPacking`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap](RankThreeSaturatedTopGap.md)
