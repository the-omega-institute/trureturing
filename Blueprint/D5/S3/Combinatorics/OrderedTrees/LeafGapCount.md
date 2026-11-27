# Counting Ordered Leaf-Gap Decorations

## Abstract

Ordered leaf-gap compositions enumerate the actual trees at every size.

**Theorem 1.1 (The actual count is the sum over skeleton sizes).**

$$a(n) = \sum_{0 \leq u < n-4} (2u+1)\operatorname{choose}\left(n+u-1, 2u+4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafGapCount.count_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural index n, a(n) is the finite cardinality of ordered rooted trees with n vertices and vertex height equal to the number of nonleaf vertices. The sum is empty when n is less than five.

For each feasible u, the 2u+1 distinct ordered skeletons of size u+3 are decorated by two mandatory terminal leaves and 2u+5 free gaps. The free gap counts have sum n−u−5. Reading gaps in order and inflating them are inverse operations. Weak composition cardinality gives the binomial coefficient for each skeleton. The two arm orientations share only the equal-arm case, which the skeleton list counts once.

## References

- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafGapCount.count_eq_sum`
- Dependency: [D5/S3/Combinatorics/OrderedTrees/LeafPruning](LeafPruning.md)
