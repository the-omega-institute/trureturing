# The exact cooling-code optimum at length 58

## Abstract

The exact optimum is 57 information classes at length 58, weight six and deletion size two.

**Theorem 1.1 (Obstruction to the group divisible design).**

$$\neg \operatorname{Nonempty}\left(\operatorname{GroupDivisibleDesign}\left(\operatorname{Fin}\left(58\right), 8, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58.no_group_divisible_design` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

There is no group divisible design on 58 points with blocks of size eight and groups of size two. Every point lies in eight blocks because each of its 56 cross-group pairs occurs once and each incident block contributes seven such pairs. Counting incidences gives 58 blocks. For the square integer point-by-block incidence matrix A, the Gram matrix is 8I + J − P, where J is the all-ones matrix and P records membership in the same group, including on the diagonal. The matrix 8I − P has 29 two-by-two diagonal blocks of determinant 48 and acts on the all-ones column by multiplication by six. The rank-one update by J multiplies the determinant by 1 + 58/6. Thus det(AAᵀ) = 2¹²¹ · 3²⁸. Its odd exponent of two contradicts det(AAᵀ) = det(A)² over the integers.

**Theorem 1.2 (Exactly 57 information classes).**

$$\operatorname{IsGreatest}\left(\{m: \mathbb{N} | \exists P \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(58\right)\right)\right),\; \operatorname{IsSupportFamily}\left(P, 6, 2\right)\}, 57\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58.support_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

In the support model every word has size six, every two-point deletion leaves a word in each class, and supports in different classes meet in at most one point. For weight six this intersection condition is equivalent to the cross-class Hamming distance being at least nine, as required for correction radius four. The projective plane over the field with seven elements has 57 points and 57 lines. Embed the points into 58 coordinates with one unused coordinate. Each line has eight points and supplies one class of all six-subsets of its points. Removing two coordinates leaves at least six points on each line, and distinct lines meet in at most one point. The finite bound gives at most 58 classes. Attaining 58 would force the design excluded above by the even-residue design criterion. Hence 57 is attained and bounds every valid family for these parameters. Section 5's question also includes other parameter choices.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58.no_group_divisible_design`
- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ExactLength58.support_optimum`
- Dependency: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign](GroupDivisibleDesign.md)
