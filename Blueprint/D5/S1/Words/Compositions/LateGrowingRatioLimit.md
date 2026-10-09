# The Late Growing Ratio Limit

## Abstract

The Shah–Kiselev permutation ratio tends to one and exceeds one at every index at least two.

For each natural index n, Phi consists of permutations of Fin (2n) that fix zero and have nonnegative suffix budgets after subtracting n. Reversing the remaining tail identifies these permutations with orderings of the integer interval from 1-n to n-1 whose prefix sums are nonnegative.

**Theorem 1.1 (Convergence from above).**

$$\operatorname{Filter}.\operatorname{Tendsto}((n: \mathbb{N} \mapsto \frac{(\operatorname{card}\left(\operatorname{phi}\left(n\right)\right): \mathbb{R})}{(\operatorname{factorial}\left((2 \cdot n - 2)\right): \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((1: \mathbb{R})\right)) \land (\forall n: \mathbb{N}, 2 \le n \implies \operatorname{factorial}\left((2 \cdot n - 2)\right) < \operatorname{card}\left(\operatorname{phi}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/LateGrowingRatioLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/shah-kiselev-2026-late-growing-ratio-limit` (proved) by `D5/S1/Words/Compositions/LateGrowingRatioLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shah-kiselev-2026-late-growing-ratio-limit","declaration_gid":"D5/S1/Words/Compositions/LateGrowingRatioLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The normalization is (2n-2) factorial. The ratio converges to one as n tends to infinity, and its numerator is strictly larger than this factorial for every n at least two. At n=1 the ratio is one.

Split a nonnegative zero-sum ordering after its last proper zero prefix. The prefix is nonnegative and the tail has strictly positive nonempty proper prefixes. Each rotation class has at most one such strictly positive ordering, and has at least one ordering with nonnegative prefixes. This compares the two counts with the factorial number of rotation classes.

Deleting a marked letter from a zero-sum subset determines the deleted letter. Applying this injection both to subsets and to their complements bounds the factorial-weighted contribution of proper zero-sum subsets by a harmonic convolution. Strong induction gives a uniform bound on the normalized counts, and the resulting harmonic error divided by the alphabet size tends to zero.

Choose a nonnegative ordering of the alphabet with zero removed. Placing zero at its beginning and at its end gives two distinct nonnegative words in the same rotation class. The map from weak words to rotation classes is then not injective, giving the strict inequality whenever n is at least two.

## References

- Truth anchor: `D5/S1/Words/Compositions/LateGrowingRatioLimit.result`
- Dependency: [D5/S1/Words/Compositions/ZeroSumWordCount](ZeroSumWordCount.md)
