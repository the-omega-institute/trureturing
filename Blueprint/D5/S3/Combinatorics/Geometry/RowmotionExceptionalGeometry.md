# Geometric exceptional states in three rows

## Abstract

Counting convex rectangle states outside the separated endpoint family.

The state space consists of actual subsets of Fin 3 times Fin n, ordered coordinatewise. An interval-closed subset contains every point between each pair of its comparable members. Native column x corresponds to source column x+1. All counts include the empty subset.

**Definition 1.1 (The complete convex state space).**

$$\forall n \in Nat,\; \forall I \in Set(Product(Fin(3), Fin(n))),\; Member(I, convexStates(n)) \Leftrightarrow OrdConnected(I)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.convexStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

convexStates(n) is the finite set of every interval-closed subset of the rectangle, with no row-nonemptiness condition.

**Definition 1.2 (The complement of separated endpoint states).**

$$\forall n \in Nat,\; \forall I \in Set(Product(Fin(3), Fin(n))),\; Member(I, exceptionalGeometry(n)) \Leftrightarrow \left(OrdConnected(I) \land \left(\neg Separated(I)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.exceptionalGeometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Separated is the existing actual-set predicate: the three rows are intervals [a(r),b(r)], both endpoint sequences are strictly decreasing, and every pair among the six indexed sites a(0),a(1),a(2),b(0)+2,b(1)+2,b(2)+2 has circular distance at least eight on the circle of length n+4. Repeated occurrences fail this condition.

**Definition 1.3 (Convex states with an empty row).**

$$\forall n \in Nat,\; \forall I \in Set(Product(Fin(3), Fin(n))),\; Member(I, missingRowStates(n)) \Leftrightarrow \left(OrdConnected(I) \land HasEmptyRow(I)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.missingRowStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HasEmptyRow(I) means that there exists r in Fin 3 such that (r,x) is absent from I for every x in Fin n. It permits other rows to be empty as well.

**Theorem 1.4 (Four endpoints suffice after an empty row).**

$$\forall n \in Nat,\; 2 \le n \Rightarrow card(missingRowStates(n)) \le 3 \cdot n^{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.missing_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least two, choose one empty row. Convexity makes each remaining row an interval. A nonempty row is encoded by its least and greatest columns; an empty row is encoded by endpoints 1 and 0. Thus every state is in the image of Fin 3 times the space of two pairs of Fin n endpoints. Multiple encodings only reduce the image cardinality.

**Theorem 1.5 (The full-carrier separated complement bound).**

$$\forall n \in Nat,\; 11 \le n \Rightarrow card(exceptionalGeometry(n)) \le 233 \cdot n^{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.exceptional_geometry_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least eleven, the number of convex states outside the separated family is at most 233 n^5. Missing-row states contribute at most 3 n^4. For a state meeting every row, convexity forces both endpoint sequences to be weakly decreasing. If all indexed shifted sites pass the distance test, equal endpoints are excluded and both sequences become strictly decreasing, giving separated endpoint data for the same actual set. Otherwise one of the fifteen indexed pairs has circular distance below eight. Fix the other five raw endpoints. The remaining shifted site has at most fifteen positions: its signed circular offset lies in the integer interval [-7,7], and raw columns inject into offsets because their interval is shorter than n+4. A fiber count and the union bound give at most 225 n^5 full-row failures. Consequently the total is at most 225 n^5+3 n^4, which is at most 233 n^5.

This is a geometric complement estimate. A bound for failures of a literal rowmotion return additionally requires the global decoder transition and return reflection. The least-positive-period bound also requires a count of the union of every shorter-return class. No assertion about these dynamics or about all separated states having the same least period follows from the complement count alone.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.convexStates`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.exceptionalGeometry`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.exceptional_geometry_bound`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.missingRowStates`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry.missing_row_bound`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder](RowmotionMatchingDecoder.md)
