# Free rotation counts of original-label orders

## Abstract

Free rotation counts of original-label orders

**Theorem 1.1 (Free rotation normalizes circular events).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall P \in \mathrm{PredicatesOn}\left(\mathrm{Cycle}\left(alpha\right)\right),\; (\mathrm{Nonempty}\left(A\right)) \Rightarrow (\mathrm{card}\left(\mathrm{RootEvent}\left(A, P\right)\right) = \mathrm{card}\left(A\right) \cdot \mathrm{card}\left(\mathrm{CircleEvent}\left(A, P\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularOrderCount.event_order_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier has decidable equality. P is any predicate on Cycle(alpha). RootEvent(A,P) filters orders(A) by P of the actual rotation class; CircleEvent(A,P) filters circles(A) by P.

An actual order of n distinct labels has n distinct rotations. The image in Mathlib Cycle retains orientation and identifies precisely those rotations. Every circle fiber therefore has exactly n rooted original-label words.

For any predicate on these circles, the number of rooted orders in that event is n times the number of event circles. The paired Good criterion is transported to such a circle predicate before this formula is used. A linear block event alone is not assumed rotation invariant.

ArcInventory(A,S) is the actual subset of circles(A) satisfying Arc A S, and sdiff(A,S) is A minus S. The carrier has decidable equality.

Orders(A) consists of the actual permutations of A.toList. Circles(A) is their image in the oriented List rotation quotient. A nonempty distinct-label word has exactly A.card distinct rotations, by the existing Mathlib rotation-freeness theorem.

**Theorem 1.2 (Count a proper arc on the actual finite circle inventory).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall S \in \mathrm{Finset}\left(alpha\right),\; ((S \subseteq A) \land ((\mathrm{Nonempty}\left(S\right)) \land (\mathrm{Nonempty}\left(\mathrm{sdiff}\left(A, S\right)\right)))) \Rightarrow (\mathrm{card}\left(\mathrm{ArcInventory}\left(A, S\right)\right) = \mathrm{factorial}\left(\mathrm{card}\left(S\right)\right) \cdot \mathrm{factorial}\left(\mathrm{card}\left(\mathrm{sdiff}\left(A, S\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularOrderCount.arc_filter_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fiber of Orders(A) onto Circles(A) has size A.card. Counting the same finite fibers gives (A.card minus 1)! actual directed circles. The boundary contraction count then counts a single arc in this very same sample space. No independence assumption or quotient of original labels enters the argument.

For a nonempty alphabet of distinct labels, event_order_card multiplies a circle-event count by A.card to recover its rooted-order count. PairedQuantitativeOrdering.quantitative_good_orders uses this equality to turn the Good-circle lower bound into a Good-order lower bound.

Only single-arc multiplicity and free rotation normalization are asserted here. Multiple-block intersections, complement-class event accounting, Bonferroni truncation and the residual tail are separate obligations before an all-rank Good-order bound can be concluded.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularOrderCount.arc_filter_card`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularOrderCount.event_order_card`
- Dependency: [D5/S3/Combinatorics/CircularWords/DisjointBlockContraction](DisjointBlockContraction.md)
