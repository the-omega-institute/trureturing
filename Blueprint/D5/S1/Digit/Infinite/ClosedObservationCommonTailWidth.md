# Complete closed graph common-tail width

## Abstract

Complete closed graph common-tail width.

**Theorem 1.1 (Finite tails before deletion).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.finite_tail_unshift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.finite_tail_unshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an exact finite bit shift of an actual address is eventually zero, the original address is also eventually zero.

**Theorem 1.2 (Reading a closed path).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.closed_path_read`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.closed_path_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A closed path has one more color than source labels. Every address realizing its full vertex and label chain reads the prescribed closed colors at the actual three-bit departure coordinates, and its successive windows give exactly the source word.

**Theorem 1.3 (Windows at shifted addresses).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.window_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.window_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first three-bit window of the address shifted by 3j bits is exactly its original window at time j.

**Theorem 1.4 (One more source step).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.original_t_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.original_t_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the original three-bit deletion after shifting by 3j bits gives the original address shifted by 3(j+1) bits.

**Theorem 1.5 (Complete closed graph common-tail width).**

Lean statement: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the original legal infinite addresses, incoming guards and three-bit deletion T. The five windows are null=000, two=100, three=010, twenty-five=101 and five=001, with translations 0,1,-t,2-t and t squared. The grouped series equals the scaled signed series, fills both guard intervals, obeys the actual branch recurrence and has unique lawful prepends. No single-valued scalar deletion is assumed.

For every b_0 in Q(t) intersect [0,lambda], the original common-denominator and bounded-conjugate parameters exist. Every admissible parameter pair gives a finite inverse-closed endpoint set, all guard-typed singleton and adjacent-interval vertices, canonical closed constraints, full successor-image unions and no dead ends.

Every finite observed graph path is jointly realized by one actual address from any chosen legal terminal tail. Conversely, every actual address has a canonical infinite graph path retaining every actual window, guard and closed color constraint. Every infinite all-containment graph path is jointly realized by one actual legal address at every time, including scalar endpoints.

For a fixed legal six-color instrument Q and every nonnegative budget, the exact attainable relation is contained in the complete closed expansion. These relations are distinct: closing an unattainable expansion endpoint does not make it an attainable target.

If 0<=b_0<lambda, two actual addresses with the same tail after M windows and the same M+1 closed colors are equal. The root images restrict unequal labels to the adjacent pairs (three,null), (null,five), (five,two) and (two,twenty-five). Every applicable closed-color width is strictly smaller than its translation gap, so a last differing window cannot exist.

For every fixed color history and every terminal vertex, all candidate paths have the same past source word. A common actual terminal tail lifts both entire paths, including singleton vertices without any finite-tail realization. The projection of all distinct vertex/word pairs H to vertices is injective. Thus H is finite and both |H| and the cardinality of its image R after deleting the global longest common prefix are at most the full vertex count.

Before any color, every guard-zero vertex has the empty source word. A nonempty history of n colors has n-1 source labels, including an already-observed terminal color. The global prefix is a prefix of every candidate word, is maximal for nonempty families and is empty for the empty family.

At lambda, common-tail uniqueness holds when the common actual tail is eventually zero. Such a tail has scalar in Z[t]. The four possible interior contacts force (-5+k+k t)/5 for k=1,2,3,4, whose nonintegral coefficient excludes that tail. Exterior contacts force the uniquely alternating nonfinite endpoint addresses. Every vertex containing an actual finite-tail scalar consequently supports at most one past word.

Every nondegenerate vertex has a legal eventually-zero realization. Truncating a legal address and completing it with zeros preserves its incoming guard. The finite window sums converge to its scalar, so some zero completion lies in the interior of any nondegenerate piece. This gives no finite-tail realization of an arbitrary singleton.

There is an actual guard-zero tail tau with scalar s*=(-4+t)/5 outside Z[t]. The lawful sources u=three tau and v=null tau are distinct, have that same actual tail and are both nonfinite. Their scalars are a-lambda and b+lambda. One fixed legal instrument can assign both cuts a and b to color one.

For every original critical endpoint graph and every such fixed instrument, inverse closure contains the guard-zero singleton {s*}. Both source singletons have all-containment edges to it. Errors +lambda and -lambda give targets a and b and color one, while tau has color zero. In the observed-terminal convention the history is [1,0], the source words are [three] and [null], and the common future starts after T tau. This exhibits at least two past words; it asserts no unbounded multiplicity.

## References

- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.closed_path_read`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.finite_tail_unshift`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.original_t_shift`
- Truth anchor: `D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth.window_shift`
- Dependency: [D5/S0/Carrier/Units](../../../S0/Carrier/Units.md)
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
- Dependency: [D5/S1/Scale/Embedding](../../Scale/Embedding.md)
