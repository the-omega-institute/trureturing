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

**Theorem 1.6 (The reverse outcome).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_count_eq_motzkin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_count_eq_motzkin` (`✓ std3`). ∎

*Citation.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Unit weights give the Motzkin number for every reverse-outcome length, including the empty case.

**Theorem 1.7 (Weighted Motzkin formula for an increasing prefix).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

For n ≥ k ≥ 0, sum the k-lift counts over the Motzkin walks of length n − k, using the number of returns as the starting rank. At n = k the empty walk contributes the k-lift count at rank zero.

**Theorem 1.8 (Catalan numbers from the lift counts).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The k-lift count at rank zero is the kth Catalan number Cₖ. Shifting the starting rank by one sends the k-lift weight to the sum of the (k − i)-lift weights with coefficients Cᵢ for 0 ≤ i ≤ k. At rank zero this identity gives the Catalan convolution, with C₀ = 1.

**Definition 1.9 (Integer shift coefficients).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients`

*Formalization.* `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

In increasing order of offset from n − k, the coefficient list represents Qₖ(T), with Q₀ = 1 and Qₖ₊₁ = T² Qₖ − T times the sum of Cᵢ Qₖ₋ᵢ for 0 ≤ i ≤ k. The Laurent shift polynomial for offsets from n is T⁻ᵏ Qₖ(T).

**Theorem 1.10 (Range of shifts).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The list has length 2k + 1 and its last coefficient is one. For k ≥ 1 the first coefficient is zero, so the nonzero shifts from n lie in [1 − k, k].

**Theorem 1.11 (Signed Motzkin formula for Question 5.2).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

For all n ≥ k ≥ 0, the coefficient at offset j weights the Motzkin number M(n − k + j). The ground-return recurrence and the Catalan rank shift give the recurrence for Qₖ, including an empty suffix. For k = 0, 1 and 2 this yields M(n), M(n + 1) − M(n), and M(n + 2) − 2M(n + 1) + M(n) − M(n − 1), as in Theorem 1.8 and Corollaries 1.9–1.10 of Clifton, Harris and Khaqan on their respective ranges. At n = k the signed sum equals Cₖ, with value one at n = k = 0.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.liftCatalan_spec`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.mem_motzkinWalks`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.motzkinWalks_nodup`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_count_eq_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.reverseOutcome_weight_eq_motzkin`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.signedCoefficients_shape`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.trace`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.walkWeight_succ_succ`
- Dependency: [D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix](BackgammonIncreasingPrefix.md)
