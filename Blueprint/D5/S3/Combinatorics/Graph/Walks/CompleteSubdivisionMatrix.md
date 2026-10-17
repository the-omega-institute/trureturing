# Symmetric binary matrices with distinct row sums

## Abstract

Symmetric binary matrices with distinct row sums

The diagonal is unrestricted. Distinct row sums force a zero row or a full row; symmetry prevents both. With a zero row, ranking the row sums gives a permutation of all indices. The ranked matrix has entry one exactly when the two ranks sum to at least n. The proof deletes the forced zero and last rows and columns and inducts by two, including both initial sizes.

**Theorem 1.1 (ranked staircase).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.ranked_staircase`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.ranked_staircase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A symmetric binary matrix whose row i sums to i has entry one exactly at positions whose indices sum to at least n.

**Theorem 1.2 (row sum le).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.row_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.row_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every binary row of length n has sum at most n.

**Theorem 1.3 (zero full incompatible).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_full_incompatible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_full_incompatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A symmetric binary matrix cannot have both a zero row and a full row.

**Theorem 1.4 (distinct rows extreme).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.distinct_rows_extreme`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.distinct_rows_extreme` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Injective row sums in a positive-size binary matrix contain either zero or n.

**Theorem 1.5 (zero row normal form).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_row_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_row_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A symmetric binary matrix with distinct row sums and a zero row admits an actual rank permutation giving the staircase and exact row ranks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.distinct_rows_extreme`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.ranked_staircase`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.row_sum_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_full_incompatible`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.zero_row_normal_form`
