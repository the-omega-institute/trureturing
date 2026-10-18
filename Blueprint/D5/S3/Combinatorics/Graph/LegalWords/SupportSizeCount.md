# The size distribution of nonadjacent supports

## Abstract

Every size fiber of actual legal Boolean words is counted by a binomial coefficient.

A legal word is a Boolean function on Fin n satisfying Adm. Its support in positions 1 through n contains i+1 exactly when the zero-based coordinate i is true. Admissibility is precisely absence of adjacent occupied coordinates, and occupationCount is the cardinality of that same support. The existing supportCount counts these actual words at a specified occupation.

**Theorem 1.1 (Uniform size-refined count).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \mathrm{supportCount}\left(n, k\right) = \mathrm{choose}\left(n + 1 - k, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/SupportSizeCount.support_count_eq_choose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural length n and natural size k, the actual fiber has cardinality choose((n+1)-k,k). Subtraction here is natural truncated subtraction. For k at most the integer quotient of n+1 by two, its upper argument is the ordinary nonnegative integer n-k+1. Above that cutoff the upper argument is strictly less than k, so the binomial coefficient is zero, including when k exceeds n+1. At k=0 the count is one for every n; at n=0 every positive-size fiber is empty.

For an arbitrary integer size z, count the same legal words satisfying the integer equality occupationCount=z. A negative z gives the empty fiber because occupation is nonnegative. For nonnegative z this fiber is exactly supportCount n z.toNat. Thus the natural-index equality has the full integer interpretation: choose(n-z+1,z) in the range from zero through floor((n+1)/2), and zero for every other integer size.

Give every position weight one in the actual forbidden-neighbour configuration polynomial. Its coefficient at degree k is supportCount n k. The existing polynomial recurrence gives the size recurrence: the count at length n+2 and size k+1 is the sum of the counts at length n+1 and size k+1, and length n and size k. The constant coefficient is one. Starting with the empty and one-position words, two-step induction and Pascal's identity yield the stated formula. The cases where truncated subtraction reaches zero are handled by the vanishing of binomial coefficients above their upper argument.

This is the distribution of support sizes. It does not assert an observation-kernel dimension or a short exact sequence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/SupportSizeCount.support_count_eq_choose`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/EdgeCount](EdgeCount.md)
