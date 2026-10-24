# Free rotation counts of original-label orders

## Abstract

Free rotation counts of original-label orders

ArcInventory(A,S) is the actual subset of circles(A) satisfying Arc A S, and sdiff(A,S) is A minus S. The carrier has decidable equality.

Orders(A) consists of the actual permutations of A.toList. Circles(A) is their image in the oriented List rotation quotient. A nonempty distinct-label word has exactly A.card distinct rotations, by the existing Mathlib rotation-freeness theorem.

**Theorem 1.1 (Count a proper arc on the actual finite circle inventory).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall S \in \mathrm{Finset}\left(alpha\right),\; ((S \subseteq A) \land ((\mathrm{Nonempty}\left(S\right)) \land (\mathrm{Nonempty}\left(\mathrm{sdiff}\left(A, S\right)\right)))) \Rightarrow (\mathrm{card}\left(\mathrm{ArcInventory}\left(A, S\right)\right) = \mathrm{factorial}\left(\mathrm{card}\left(S\right)\right) \cdot \mathrm{factorial}\left(\mathrm{card}\left(\mathrm{sdiff}\left(A, S\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularOrderCount.arc_filter_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fiber of Orders(A) onto Circles(A) has size A.card. Counting the same finite fibers gives (A.card minus 1)! actual directed circles. The boundary contraction count then counts a single arc in this very same sample space. No independence assumption or quotient of original labels enters the argument.

Only single-arc multiplicity and free rotation normalization are asserted here. Multiple-block intersections, complement-class event accounting, Bonferroni truncation and the residual tail are separate obligations before an all-rank Good-order bound can be concluded.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularOrderCount.arc_filter_card`
- Dependency: [D5/S3/Combinatorics/CircularWords/DisjointBlockContraction](DisjointBlockContraction.md)
