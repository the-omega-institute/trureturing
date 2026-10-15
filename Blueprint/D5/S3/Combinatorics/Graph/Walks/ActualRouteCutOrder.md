# Ordered Cuts in an Actual Joined Route

## Abstract

Actual piece order and literal route support earn strict cut order and the concrete three fragments.

The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.

**Theorem 1.1 (Identify the Supplied Actual Route).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_ordered_path_is_join`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_ordered_path_is_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native adjacency supplies a Linked witness for the supplied ordered pieces. Equality of the supplied path support with their literal joined support then identifies the actual walks, keeping subsequent slicing on that same route.

**Theorem 1.2 (Earn the Strict Cut Order).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_cut_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_cut_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Directed cuts lie at valid local edge indices in two different route pieces. Literal full support locates them in the joined walk; the earlier piece contributes a smaller global index. The strict order and both directed endpoint pairs are conclusions.

**Theorem 1.3 (Slice the Same Actual Joined Route).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_two_cut_slicing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_two_cut_slicing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the two-cut construction at the just-earned strict indices of the supplied simple joined route. Three actual simple fragments retain its complete support and precisely its edges other than the two supplied cuts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_cut_order`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_joined_route_two_cut_slicing`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.actual_ordered_path_is_join`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering](ActualCyclePieceReordering.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing](OrderedTwoCutSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
