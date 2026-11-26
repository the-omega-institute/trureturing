# Changes of strict crossing parity

## Abstract

Bound how often strict crossing parity can change across an ordered list of ranks.

**Definition 1.1 (Strict crossings on the observed ranks).**

$$\operatorname{PaddedParity}\left(j\right) = \operatorname{PaddedStrictCrossingsModTwo}\left(j\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity.paddedParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation at slot j for 1 ≤ j ≤ n is cut j−1. An indexed interval contributes exactly when its lower endpoint is strictly below the cut and its upper endpoint is strictly above it. PaddedStrictCrossingsModTwo is the number of contributing indices modulo two at such slots and zero at all other natural-number slots.

**Theorem 1.2 (Every interval supplies at most two changes of cut parity).**

$$\operatorname{AdjacentChanges}\left(p\right) \le \operatorname{TwiceCardinality}\left(I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity.changes_le_twice_jumps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite index type, let n be a natural number and take a monotone list of n natural-number cuts. Each index has two natural-number endpoints. The sequence p consists of the strict crossing parities at these cuts, with zero at both ends. AdjacentChanges(p) counts neighboring unequal entries, including both padding boundaries. TwiceCardinality(I) is twice the number of indices.

The cuts strictly between the endpoints occupy a contiguous block. If no block starts or ends at a boundary then every index gives the same contribution on either side, so parity does not change there. Counting endpoints with multiplicity gives the bound. For example, at three cuts parities one, zero, one require four changes and hence at least two intervals. Degree and support constraints must be checked independently when constructing a factor.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity.changes_le_twice_jumps`
- Truth anchor: `D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity.paddedParity`
