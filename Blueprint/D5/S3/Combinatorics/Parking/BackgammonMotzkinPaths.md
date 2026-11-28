# Backgammon outcomes and Motzkin walks

## Abstract

The ground-return recurrence for ordinary Motzkin walks gives weighted and signed counts of increasing-prefix backgammon outcomes.

**Definition 1.1 (Scan a Motzkin step word).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.trace`

*Formalization.* `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.trace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The scan counts each arrival at height zero, including the final endpoint of a nonempty walk. A down step at height zero fails.

**Theorem 1.2 (Literal Motzkin walks).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.mem_motzkinWalks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.mem_motzkinWalks` (`✓ std3`). ∎

*Citation.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

At length m the enumerator contains precisely the words that never leave nonnegative height and finish at height zero.

**Theorem 1.3 (Each step word occurs once).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.motzkinWalks_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.motzkinWalks_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

An upward first step determines the unique return that closes the first arch, and the cut fixes its interior and the remaining walk.

**Theorem 1.4 (Ground returns under horizontal steps and arches).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.walkWeight_succ_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.walkWeight_succ_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

An initial horizontal step adds one ground return. To create an initial arch, cut a shorter walk at any ground visit, using both endpoints as possible cuts. The cut leaves one resulting walk of each rank from 1 through one more than the shorter walk's rank. This is the weighted form of Lemma 3.18, equation (5), of Clifton, Harris and Khaqan.

**Theorem 1.5 (Equality by rank).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_weight_eq_motzkin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_weight_eq_motzkin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Every weight on the longest distinct initial preference length gives the same sum as the weight on ground returns. This uses the refinement in the proof of Theorem 1.8. For nonempty walks, the rank exceeds the number of interior touches by one.

**Theorem 1.6 (Weighted Motzkin formula for an increasing prefix).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

For n ≥ k ≥ 0, sum the k-lift counts over the Motzkin walks of length n − k, using the number of returns as the starting rank. At n = k the empty walk contributes the k-lift count at rank zero.

**Theorem 1.7 (Catalan numbers from the lift counts).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The k-lift count at rank zero is the kth Catalan number Cₖ. Shifting the starting rank by one sends the k-lift weight to the sum of the (k − i)-lift weights with coefficients Cᵢ for 0 ≤ i ≤ k. At rank zero this identity gives the Catalan convolution, with C₀ = 1.

**Definition 1.8 (Integer shift coefficients).**

$$Q_{0}=1,\quad Q_{k + 1}=T^{2}Q_{k}-T\sum_{i=0}^{k} C_{i}Q_{k - i}$$

*Formalization.* `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Read the list from the constant term upward as the coefficients of Qₖ(T). Here Cᵢ is the Catalan number liftCatalan(i). The recurrence first shifts the previous coefficient list by two positions, then subtracts the Catalan-weighted lists shifted by one position. The Laurent polynomial for offsets from n has the coefficients of Qₖ shifted down by k.

**Theorem 1.9 (Range of shifts).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The list has length 2k + 1 and its last coefficient is one. For k ≥ 1 the first coefficient is zero, so the nonzero shifts from n lie in [1 − k, k].

**Theorem 1.10 (Signed Motzkin formula for Question 5.2).**

$$|\operatorname{outcomeWords}\left(\operatorname{withIncreasingPrefix}\left(k, \operatorname{reverseOutcome}\left(n - k\right)\right)\right)|=\sum_{j=0}^{2k} \operatorname{signedCoefficients}\left(k\right)[j]\cdot|\operatorname{motzkinWalks}\left(n - k + j\right)|,\quad n\geq k\geq0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Clifton, Harris and Khaqan ask in Question 5.2 for a sum involving Motzkin numbers with indices depending on n, for each fixed k and n > k. The target outcome has the labels 1 through k in increasing order followed by the remaining labels in decreasing order. The formula holds for all n ≥ k ≥ 0. Vertical bars count list entries, the square brackets index signedCoefficients from zero, and the arithmetic of the sum is over the integers. The ground-return recurrence and the Catalan rank shift give the recurrence for Qₖ. For k = 0, 1 and 2 the formula yields M(n), M(n + 1) − M(n), and M(n + 2) − 2M(n + 1) + M(n) − M(n − 1), where M counts ordinary Motzkin walks. These are Theorem 1.8 and Corollaries 1.9–1.10 on their published ranges. At n = k the suffix is empty and the sum is Cₖ, agreeing with the identity-permutation case of Theorem 1.6 for positive k. The empty street contributes one.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.mem_motzkinWalks`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.motzkinWalks_nodup`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_weight_eq_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.trace`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.walkWeight_succ_succ`
- Dependency: [D5/S3/Combinatorics/Parking/BackgammonReverseWeights](BackgammonReverseWeights.md)
