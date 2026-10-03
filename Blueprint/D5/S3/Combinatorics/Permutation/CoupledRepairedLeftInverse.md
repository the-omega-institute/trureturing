# Left composition of the coupled repaired digit maps

## Abstract

The coupled repaired digit construction has bounded forward digits and recovers both original permutations under the first front and back bounds.

Permutations use zero-based labels. The original column count is k plus one, the original row count is k plus two, and the first front threshold is L plus one. The parameters satisfy L at most B and B at most k plus one.

**Definition 1.1 (Deletion and standardization).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.cut`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.cut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Delete the entry at the selected position and standardize the surviving labels in increasing order.

**Definition 1.2 (Insertion and lifting).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.put`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.put` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Lift the surviving labels past the inserted label and insert it at the selected position.

**Definition 1.3 (Low-row positions).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.Slots`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.Slots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The low slots are the positions whose permutation values are strictly below the threshold T.

**Definition 1.4 (Increasing enumeration of low slots).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.slotOrder`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.slotOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For T at most the permutation size, enumerate its T low slots in increasing position order.

**Definition 1.5 (Ordered low subword).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.lowWord`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.lowWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Read the permutation values at the increasingly enumerated low slots. This gives a permutation of the labels strictly below T.

**Definition 1.6 (Replacement in fixed low slots).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.replace`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.replace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Replace the low subword by the supplied permutation while preserving its positions and all high entries.

**Definition 1.7 (The coupled digit maps).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actualAlgorithms`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actualAlgorithms` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For the forward map, set t to the first column value, delete the row at t and the first column entry, and read the original low subword on labels zero through L. Delete its maximum L and replace the ordinary tail's low subword by the resulting word. The digit d counts the entries after that maximum; b counts the ordinary tail entries before t whose labels are below B. For the inverse map, read the repaired low subword, insert its maximum L at position L minus d, and select t as low slot number b below B. Count the low slots below L before t to identify the deleted label and the original low subword, then undo the row and column deletions.

**Theorem 1.8 (Recovery of the original pair).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actual_full_left_composition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actual_full_left_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For all nonnegative integers k, L and B with L at most B and B at most k plus one, let sigma permute the k plus two row labels and pi permute the k plus one column labels. Set t to pi evaluated at zero. Assume sigma at row position t is below L plus one, and sigma at the following row position t plus one is below B plus one. If z is the forward output, its digits satisfy d less than L plus one and b less than B, and applying the inverse to the repaired tail and these digits returns exactly sigma and pi. The B-slot prefix count recovers t. Deletion transports the ordered low slots, and their prefix count recovers the deleted label; these recover the row subword and then both full permutations. The first and last insertion positions, L equal to zero, and k equal to zero are included.

This identity concerns the literal permutation maps. The opposite composition, preservation of all board eligibility conditions, the integer weight identity, iteration, and matrix or tensor enumeration require additional results.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.Slots`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actualAlgorithms`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.actual_full_left_composition`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.cut`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.lowWord`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.put`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.replace`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.slotOrder`
