# Counting normalized fork decorations

## Abstract

Two bounded binomial sums give the actual unordered rooted-tree count.

**Theorem 1.1 (The equal-arm and unequal-arm contributions).**

$$\forall n \in \mathbb{N}, a(n) = \sum_{b,m : b+5+2m \leq n} \operatorname{choose}\left(n-4-2m, b+1\right) + \sum_{1 \leq u \leq n-5} u\operatorname{choose}\left(n-3, u+2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ForkCount.count_by_arms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum indices are natural numbers. In the equal-arm case m is the smaller tip offset. The difference between the tip offsets and the b+1 spine counts are b+2 free slots of total n−b−5−2m. The resulting binomial counts also include the diagonal pair.

With unequal arms and u=b+c, there are u choices of positive c. The u+1 spine counts and two tip offsets give u+3 free slots of total n−u−5. The Lean unequal-arm sum uses v=u−1 and range(n−5). All subtractions inside the binomials are taken on the indicated feasible ranges, including empty ranges at small n.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.count_by_arms`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/ForkDecoration](ForkDecoration.md)
