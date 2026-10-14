# Sun's weighted distinct-sum conjecture

## Abstract

Sun's weighted distinct-sum bound is refuted over the rationals at n = 2 by the set {0, 1, 2}.

Zhi-Wei Sun, "On permutations of {1,...,n} and related topics", J. Algebraic Combin. 54 (2021) 893–912, Conjecture 4.9, page 18, states verbatim: "Conjecture 4.9. Let n ∈ Z+ and let F be a field with p(F) > n + 1, where p(F) = p if the characteristic of F is a prime p, and p(F) = +∞ if the characteristic of F is zero. Let A be any finite subset of F with |A| ⩾ n + δ_{n,3}, where δ_{n,3} is 1 or 0 according as n = 3 or not. Then, for the set S(A) := {Σ_{k=1}^n k a_k : a_1, . . . , a_n are distinct elements of A} (4.8), we have |S(A)| ⩾ min{p(F), (|A| − n) n(n+1)/2 + n(n²−1)/6 + 1}. (4.9)"

**Definition 1.1 (The characteristic bound).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)], \operatorname{pF}\left(F\right) = \text{if} \operatorname{ringChar}\left(F\right) = 0 \text{then} \operatorname{top} \text{else} (\operatorname{ringChar}\left(F\right) : \operatorname{WithTop}\left(\mathbb{N}\right))$$

*Formalization.* `D5/S3/Arith/Additive/SunWeightedDistinctSums.pF` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *On permutations of {1,...,n} and related topics*. DOI: [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8). URL: <https://arxiv.org/abs/1811.10503v6>.

*Commentary.*

The value pF F is top when ringChar F is zero and is the natural cast of ringChar F otherwise. This is the paper's p(F), with top representing +∞.

**Definition 1.2 (Weighted distinct sums).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)], [\operatorname{DecidableEq}\left(F\right)], \forall A \in \operatorname{Finset}\left(F\right),\; \forall n \in \mathbb{N},\; \operatorname{weightedDistinctSums}\left(A, n\right) = \operatorname{Finset}.\operatorname{image}\left(\text{fun} a \mapsto \sum_{k : \operatorname{Fin}\left(n\right)} (\operatorname{val}\left(k\right) + 1 : F) \cdot (\operatorname{a}\left(k\right) : F), (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Function}.\operatorname{Embedding}\left(\operatorname{Fin}\left(n\right), A\right)\right))\right)$$

*Formalization.* `D5/S3/Arith/Additive/SunWeightedDistinctSums.weightedDistinctSums` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *On permutations of {1,...,n} and related topics*. DOI: [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8). URL: <https://arxiv.org/abs/1811.10503v6>.

*Commentary.*

For a finite set A in a field and a natural n, weightedDistinctSums A n is the image of all embeddings of Fin n into the subtype of A under the sum whose kth coefficient is k+1. The embeddings enforce that the selected elements are distinct members of A.

**Definition 1.3 (The numerical lower bound).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{sunBound}\left(m, n\right) = \left(m - n\right) \cdot \operatorname{Nat}.\operatorname{div}\left(n \cdot \left(n + 1\right), 2\right) + \operatorname{Nat}.\operatorname{div}\left(n \cdot \left(n^{2} - 1\right), 6\right) + 1$$

*Formalization.* `D5/S3/Arith/Additive/SunWeightedDistinctSums.sunBound` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *On permutations of {1,...,n} and related topics*. DOI: [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8). URL: <https://arxiv.org/abs/1811.10503v6>.

*Commentary.*

sunBound m n is the natural-number expression (m−n)n(n+1)/2 + n(n²−1)/6 + 1 from (4.9). Natural-number division is floor division.

**Definition 1.4 (Conjecture 4.9).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)], [\operatorname{DecidableEq}\left(F\right)], \forall n \in \mathbb{N},\; 1 \le n \Rightarrow ((n : \operatorname{WithTop}\left(\mathbb{N}\right)) + 1 < \operatorname{pF}\left(F\right) \Rightarrow (\forall A \in \operatorname{Finset}\left(F\right),\; n + (\text{if} n = 3 \text{then} 1 \text{else} 0) \le \operatorname{Finset}.\operatorname{card}\left(A\right) \Rightarrow (\operatorname{min}\left(\operatorname{pF}\left(F\right), (\operatorname{sunBound}\left(\operatorname{Finset}.\operatorname{card}\left(A\right), n\right) : \operatorname{WithTop}\left(\mathbb{N}\right))\right) \le (\operatorname{Finset}.\operatorname{card}\left(\operatorname{weightedDistinctSums}\left(A, n\right)\right) : \operatorname{WithTop}\left(\mathbb{N}\right)))))$$

*Formalization.* `D5/S3/Arith/Additive/SunWeightedDistinctSums.claim` (`✓ std3`).

*Citation.* Zhi-Wei Sun (2021). *On permutations of {1,...,n} and related topics*. DOI: [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8). URL: <https://arxiv.org/abs/1811.10503v6>.

*Commentary.*

The displayed proposition is Conjecture 4.9 with the field, characteristic, cardinality and weighted-sum notation written explicitly. The source's δn,3 is encoded by the conditional if n = 3 then 1 else 0.

**Theorem 1.5 (The conjecture is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/SunWeightedDistinctSums.result` (`✓ std3`). ∎

*Resolves.* `Problems/sun-2021-conjecture-4-9-weighted-distinct-sums` (refuted) by `D5/S3/Arith/Additive/SunWeightedDistinctSums.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sun-2021-conjecture-4-9-weighted-distinct-sums","declaration_gid":"D5/S3/Arith/Additive/SunWeightedDistinctSums.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2021). *On permutations of {1,...,n} and related topics*. DOI: [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8). URL: <https://arxiv.org/abs/1811.10503v6>.

*Commentary.*

At F = ℚ, n = 2 and A = {0,1,2}, the six ordered pairs give the values 2, 4, 1, 5, 2, 4. Thus the distinct sums are {1,2,4,5}, of cardinality 4, while sunBound 3 2 is 5; the claimed inequality would be 5 ≤ 4, a contradiction.

## References

- Truth anchor: `D5/S3/Arith/Additive/SunWeightedDistinctSums.claim`
- Truth anchor: `D5/S3/Arith/Additive/SunWeightedDistinctSums.pF`
- Truth anchor: `D5/S3/Arith/Additive/SunWeightedDistinctSums.result`
- Truth anchor: `D5/S3/Arith/Additive/SunWeightedDistinctSums.sunBound`
- Truth anchor: `D5/S3/Arith/Additive/SunWeightedDistinctSums.weightedDistinctSums`
