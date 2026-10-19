# The diagonal-aware selection matrix

## Abstract

The diagonal-aware selection matrix

The diagonal records selected original vertices and the off-diagonal records selected midpoints. Both come from the same arbitrary landmark set. Each entry is binary, the matrix is symmetric, and its row sum is the selected incident-midpoint count plus the original selection bit. The diagonal is free; it is not an irreflexive adjacency predicate.

**Definition 1.1 (pairBit).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The off-diagonal integer bit records the selected midpoint; its diagonal is zero.

**Theorem 1.2 (selectedDegree eq sum pairBit).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selectedDegree_eq_sum_pairBit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selectedDegree_eq_sum_pairBit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Each selected midpoint incident with u corresponds to exactly one other original index, so the selected degree equals the off-diagonal row sum.

**Theorem 1.3 (pairBit symm).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The selected off-diagonal bits are symmetric under exchanging original indices.

**Theorem 1.4 (pairBit binary).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_binary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every off-diagonal bit is zero or one.

**Definition 1.5 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The natural-valued selection matrix uses original bits on its diagonal and midpoint bits off the diagonal.

**Theorem 1.6 (selection symm).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The actual landmark selection matrix is symmetric, including its independent diagonal.

**Theorem 1.7 (selection binary).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_binary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Every selection entry is at most one.

**Theorem 1.8 (selection diagonal).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer coercion of a diagonal entry is exactly the original selection bit.

**Theorem 1.9 (selection offDiagonal).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_offDiagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_offDiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer coercion of an off-diagonal entry is exactly the selected midpoint bit.

**Theorem 1.10 (selection row).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer row sum is the selected midpoint degree plus the original selection bit.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_binary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.pairBit_symm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selectedDegree_eq_sum_pairBit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_binary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_diagonal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_offDiagonal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_row`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.selection_symm`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting](CompleteSubdivisionCounting.md)
