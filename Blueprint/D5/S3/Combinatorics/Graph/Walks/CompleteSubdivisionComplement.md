# Complementing all landmarks

## Abstract

Complementing all landmarks

The full-vertex distance histogram is independent of the actual graph edge. Each selected bin plus its complementary bin equals that full bin. Hence a pair of edges has equal profiles for a landmark set exactly when it has equal profiles for its complement. Complementation flips every selection-matrix entry, including the diagonal.

**Theorem 1.1 (full selectedDegree).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_selectedDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_selectedDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

With all vertices selected, every original is incident with exactly n-1 selected midpoints.

**Theorem 1.2 (full bins equal).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_bins_equal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_bins_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

For the full vertex set, every actual graph edge has the same four distance-bin counts.

**Theorem 1.3 (bin add compl).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.bin_add_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.bin_add_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A selected bin and its full-vertex complement sum to the corresponding full bin.

**Theorem 1.4 (profile compl iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.profile_compl_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.profile_compl_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Equal profiles of actual graph edges are preserved and reflected by complementing all landmarks.

**Theorem 1.5 (resolves compl iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.resolves_compl_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.resolves_compl_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A full-vertex landmark subset resolves exactly when its complement resolves.

**Theorem 1.6 (selection compl).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Complementing the landmark set flips every matrix entry, including the diagonal.

**Theorem 1.7 (selection row compl).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_row_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_row_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Complementary row sums add to n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.bin_add_compl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_bins_equal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.full_selectedDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.profile_compl_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.resolves_compl_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_compl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.selection_row_compl`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection](CompleteSubdivisionSelection.md)
