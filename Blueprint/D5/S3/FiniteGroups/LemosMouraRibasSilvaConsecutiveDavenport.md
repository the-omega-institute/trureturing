# Consecutive Davenport constants of finite groups

## Abstract

The consecutive Davenport constant of every finite group equals its order.

**Definition 1.1 (A consecutive product-one subsequence).**

$$\forall G \in Type,\; [Monoid\left(G\right)] \forall S \in List\left(G\right),\; HasConsecutiveProductOne\left(S\right) \Leftrightarrow (\exists T \in List\left(G\right),\; T \ne [] \land (\operatorname{List.IsInfix}\left(T, S\right) \land \operatorname{List.prod}\left(T\right) = 1))$$

*Formalization.* `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.HasConsecutiveProductOne` (`✓ std3`).

*Citation.* A. Lemos, A. O. Moura, S. Ribas and A. T. Silva (2024). *A note on weighted consecutive Davenport constant*. DOI: [10.48550/arXiv.2404.11312](https://doi.org/10.48550/arXiv.2404.11312). URL: <https://arxiv.org/abs/2404.11312v1>.

*Commentary.*

Printed p. 1 states: “An ordered subsequence T of S is an ordered sequence of the form T = gᵢ · gᵢ₊₁ · … · gⱼ₋₁ · gⱼ for some 1 ≤ i ≤ j ≤ k.” Printed p. 2 states: “When A = {1}, we call S a consecutive product-one sequence and a consecutive product-one free sequence, respectively.” Ordered sequences are List G. The condition T ≠ [] excludes the empty block, List.IsInfix T S specifies contiguity, and List.prod T multiplies letters in their given order. The definition also makes sense for a monoid.

**Definition 1.2 (The unweighted consecutive Davenport constant).**

$$\forall G \in Type,\; [Monoid\left(G\right)] C\left(G\right) = sInf\left(\{ l : Nat \mid 0 < l \land (\forall S \in List\left(G\right),\; l \le \operatorname{List.length}\left(S\right) \Rightarrow HasConsecutiveProductOne\left(S\right)) \}\right)$$

*Formalization.* `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.C` (`✓ std3`).

*Citation.* A. Lemos, A. O. Moura, S. Ribas and A. T. Silva (2024). *A note on weighted consecutive Davenport constant*. DOI: [10.48550/arXiv.2404.11312](https://doi.org/10.48550/arXiv.2404.11312). URL: <https://arxiv.org/abs/2404.11312v1>.

*Commentary.*

Printed p. 2 states: “Let C_A(G) be the smallest positive integer ℓ such that every sequence over G, with length at least ℓ, has an A-weighted consecutive product-one subsequence.” “For A = {1}, we omit the index A.” Here C G is sInf in the natural numbers of the positive thresholds with this property. The threshold set is nonempty for every finite group by the prefix-product pigeonhole principle; thus its infimum is its least element. The natural infimum of an empty threshold set is zero.

**Definition 1.3 (Conjecture 3.4).**

$$claim \Leftrightarrow (\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] C\left(G\right) = \operatorname{Nat.card}\left(G\right))$$

*Formalization.* `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.claim` (`✓ std3`).

*Citation.* A. Lemos, A. O. Moura, S. Ribas and A. T. Silva (2024). *A note on weighted consecutive Davenport constant*. DOI: [10.48550/arXiv.2404.11312](https://doi.org/10.48550/arXiv.2404.11312). URL: <https://arxiv.org/abs/2404.11312v1>.

*Commentary.*

Printed p. 3 states: “For every finite group G, it holds C(G) = |G|.” The carrier G has Group and Finite instances, and Nat.card G denotes its order. This includes the trivial group.

**Theorem 1.4 (Conjecture 3.4 holds).**

$$\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] C\left(G\right) = \operatorname{Nat.card}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result` (`✓ std3`). ∎

*Resolves.* `Problems/lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4` (proved) by `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4","declaration_gid":"D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Lemos, A. O. Moura, S. Ribas and A. T. Silva (2024). *A note on weighted consecutive Davenport constant*. DOI: [10.48550/arXiv.2404.11312](https://doi.org/10.48550/arXiv.2404.11312). URL: <https://arxiv.org/abs/2404.11312v1>.

*Commentary.*

A word of length at least Nat.card G has two equal prefix products, so the intervening nonempty contiguous block has product one. For the converse, enumerate the group as e(0), …, e(n−1) and take successive letters e(i)⁻¹e(i+1). The prefix products are e(0)⁻¹e(i), which are pairwise distinct. Consequently this word of length n−1 has no nonempty product-one block. These upper and lower bounds identify the least positive threshold. The argument uses arbitrary finite groups and does not require commutativity or metacyclic structure. Larger weight sets and the enumeration of extremal words are outside this statement.

## References

- Truth anchor: `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.C`
- Truth anchor: `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.HasConsecutiveProductOne`
- Truth anchor: `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.claim`
- Truth anchor: `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction](NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction.md)
