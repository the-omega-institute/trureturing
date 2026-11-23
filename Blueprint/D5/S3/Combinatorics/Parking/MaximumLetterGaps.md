# Maximum-letter gaps in bounded parking words

## Abstract

Deletion of the maximum letter gives an ordered gap profile and a shorter bounded parking word.

**Definition 1.1 (The sorted rank test).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.RankBound`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.RankBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

At every zero-based index i, the letter at i is at most i + 1.

**Definition 1.2 (Bounded parking words).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.BoundedParking`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.BoundedParking` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The word has length n, each letter is in 1 through m, and sorting the word in ascending order satisfies the rank test.

**Definition 1.3 (The maximum-letter fiber).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Original`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Original` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A bounded parking word at length n and bound m whose letter m occurs exactly r times.

**Definition 1.4 (The retained word and its profile).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Retained`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Retained` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

A bounded parking word at length n − r and bound m − 1 together with an ordered list of n − r + 1 nonnegative gap sizes summing to r.

**Theorem 1.5 (The rank test through gap insertion).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.sorted_prefix_membership`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/MaximumLetterGaps.sorted_prefix_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For 2 ≤ m ≤ n and 1 ≤ r ≤ n − m + 1, insert a total of r copies of m into the ordered gaps of a word of length n − r with letters strictly below m. The reconstructed word is bounded parking exactly when the retained word passes the shorter test. In sorted order the added letters form a final constant block, and its first rank is n − r + 1.

**Theorem 1.6 (Maximum-letter multiplicity cutoff).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.max_count_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/MaximumLetterGaps.max_count_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

In a bounded parking word with m ≤ n, at most n − m + 1 letters equal m. If m occurs, its first sorted occurrence has rank n − r + 1 for multiplicity r.

**Definition 1.7 (Delete the maximum letters).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.delete`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.delete` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Scan the actual word to keep its nonmaximum letters and count copies of m in each gap, including both ordered boundary gaps.

**Definition 1.8 (Reconstruct from the gap profile).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.insert`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.insert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Put the specified number of copies of m into each of the ordered gaps. The sorted-prefix equivalence proves membership in the maximum-letter fiber.

**Definition 1.9 (The deletion and insertion equivalence).**

Lean statement: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.parkingGapEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/MaximumLetterGaps.parkingGapEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The two operations are inverse for each admissible n, m and positive r. The replay law for unary gaps recovers the original word, and reading the profile of a reconstructed word recovers the retained word and every gap size.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.BoundedParking`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Original`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.RankBound`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.Retained`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.delete`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.insert`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.max_count_cut`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.parkingGapEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/MaximumLetterGaps.sorted_prefix_membership`
- Dependency: [D5/S1/Words/UnaryGapWords](../../../S1/Words/UnaryGapWords.md)
