# Counting good permutations

## Abstract

Exact good-permutation counts in every positive dimension.

Arrays are equivalences (Fin m × Fin n) ≃ Fin (m*n), and entry adds one to each rank. Good and Structure are the predicates of OnnGoodPermutationStructure. Nat.card counts the finite subtype of equivalences. All subtractions and powers below are natural-number operations.

**Definition 1.1 (The number of good rank arrays).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{goodCount}\left(m, n\right) = \operatorname{Nat.card}\left(\{s:((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right))|\operatorname{Good}\left(s\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.goodCount` (`✓ std3`).

*Citation.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Section 2, page 4, immediately before Lemma 2.2: “An interesting question suggested by a referee is to count and characterize, for every m and n, those permutations which are good for all 1≤i<m and 1≤j<n.” Each equivalence supplies exactly one placement of the labels 1,…,mn.

**Definition 1.2 (The four counting cases).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{proposedCount}\left(m, n\right) = if (\operatorname{min}\left(m, n\right) = 1) then \operatorname{Nat.factorial}\left(\operatorname{max}\left(m, n\right)\right) else (if (\operatorname{min}\left(m, n\right) = 2) then 2^{2 \cdot \operatorname{max}\left(m, n\right) - 1} else (if ((m = 3) \land (n = 3)) then 72 else (0)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.proposedCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

The smaller dimension selects the factorial and power-of-two cases. The remaining positive cases give 72 for three by three and zero otherwise.

**Definition 1.3 (The proposed count and characterization).**

$$claim = (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < m) \Rightarrow ((0 < n) \Rightarrow ((\operatorname{goodCount}\left(m, n\right) = \operatorname{proposedCount}\left(m, n\right)) \land (\forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; (\operatorname{Good}\left(s\right)) \Leftrightarrow (\operatorname{Structure}\left(s\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

Section 2, page 4, immediately before Lemma 2.2: “An interesting question suggested by a referee is to count and characterize, for every m and n, those permutations which are good for all 1≤i<m and 1≤j<n.” The published source asks the question; the proposed answer displayed here supplies the exact counts and characterization. The quantifiers range over all positive natural dimensions and every rank array in either orientation. The two-row split is unique, including its endpoint cases; the three-by-three alternatives are the two ordered-list types.

**Theorem 1.4 (The count and characterization in all dimensions).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < m) \Rightarrow ((0 < n) \Rightarrow ((\operatorname{goodCount}\left(m, n\right) = \operatorname{proposedCount}\left(m, n\right)) \land (\forall s \in ((\operatorname{Fin}\left(m\right)\times\operatorname{Fin}\left(n\right))\equiv\operatorname{Fin}\left(m \cdot n\right)),\; (\operatorname{Good}\left(s\right)) \Leftrightarrow (\operatorname{Structure}\left(s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-onn2023good` (proved) by `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-onn2023good","declaration_gid":"D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shmuel Onn (2023). *On Supmodular Matrices*. DOI: [10.48550/arXiv.2309.07700](https://doi.org/10.48550/arXiv.2309.07700). URL: <https://arxiv.org/abs/2309.07700v1>.

*Commentary.*

A unique sign transition splits a good two-row array into two disjoint chains. Their label sets run through all even subsets of Fin (2*n), giving 2^(2*n−1). The two three-by-three types have center label 5 and two independent interleavings of two ordered pairs, hence 36 each. One-dimensional arrays contribute every permutation; overlapping three-by-three blocks exclude the remaining dimensions.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.goodCount`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.proposedCount`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.result`
- Dependency: [D5/S1/Words/Patterns/A398542FixedBottom](../../../S1/Words/Patterns/A398542FixedBottom.md)
- Dependency: [D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure](OnnGoodPermutationStructure.md)
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/EvenBridge](../SubsetSpectrum/EvenBridge.md)
