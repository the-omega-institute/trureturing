# An actual retained original-tuple bound

## Abstract

The original retained long-chart tuple count consumes the actual record reconstruction and physical bad-degree average, with no supplied endpoint family or counting bound.

**Theorem 1.1 (Average the defect in the original six-word count).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalRetainedCount.actual_retained_long_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalRetainedCount.actual_retained_long_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each epsilon>0 one C works for every prime p, positive H with H^2=XY and H>=p, widths 1<=X<=Y with 3Y<p^2 and XY<2p^4, and the stated numerical separation conditions. Fix the original alternating units. T consists of actual bounded six-return rows with word minus the identity, unit middle entries and unit endpoint first coordinates. Reduced bases are supplied only for actual middle pairs in T.image originalMiddle; they must be long and have unit first shortest-vector coordinate, and the original right side 1+a1*a2*t*w is a unit. Then, with A=XY and L=1+log(2p)/log 2, the actual count is at most C*p^epsilon*(A+(A/p)*L+A^2/p^4)+sqrt(C*p^epsilon*A^6*L/p^15).

Apply actual_retained_rows_dyadic_count, which constructs the actual coordinate endpoint fibers from T and proves that their cardinalities sum exactly to |T|. Every middle pair lies in the literal X,Y rectangle; an explicit integer-interval count bounds the number of such parameters by 9XY. Apply actual_long_bad_degree_average to those same actual fibers, using the reconstructed anchors, original word, endpoint units and boxes. There is no second independently supplied endpoint set or weight budget. The resulting defect contributes the first term. Insert the proved 9XY parameter count into the dyadic square-root term and normalize XY*(XY/p^3)^5=(XY)^6/p^15. A single positive constant dominates both contributions.

The three numerical hypotheses are (32A/p^3)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p. They remain explicit here. Deriving them from the original A<=C0*p^(18/5) range, absorbing the displayed powers and logarithms, adding every removed chart and passing from minus the identity to all scalar centers are separate arguments needed for the complete original conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalRetainedCount.actual_retained_long_tuple_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage](PascadiOriginalBadDegreeAverage.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalRetainedRows](PascadiOriginalRetainedRows.md)
