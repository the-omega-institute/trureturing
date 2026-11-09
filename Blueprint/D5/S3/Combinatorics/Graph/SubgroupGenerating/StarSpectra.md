# StarSpectra

## Abstract

Actual star spectra with multiplicity.

**Definition 1.1 (Constant arrow matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.arrowMatrix`

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.arrowMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For every finite leaf type alpha with decidable equality, arrowMatrix a b c has central diagonal a, leaf diagonal b, center-to-leaf and leaf-to-center entries c, and zero entries between different leaves. The carrier is Unit disjoint-union alpha.

**Definition 1.2 (Complete star eigenvalue lists).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.starValues`

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.starValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For zero leaves the multiset is the singleton zero. For r positive leaves, adjacency has sqrt(r), -sqrt(r), and r-1 zeroes; L and Q have 0, r+1, and r-1 ones; CN has 0, r-1, and r-1 copies of -1. The zero and one leaf cases retain all vertices and multiplicities.

**Theorem 1.3 (The literal four star matrices).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

The source matrices of the star centered at inl(()) equal the displayed arrow matrices. Adjacency uses (0,0,1), Laplacian uses (r,1,-1), and the explicitly defined signless matrix uses (r,1,1). CN has a zero center block and the leaf block J-I. The degree and common-neighbor identities count the actual neighbor sets.

**Theorem 1.4 (Actual star spectra with multiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For every finite leaf type alpha, decidable equality and every matrix kind, the actual Hermitian eigenvalue multiset of the star on Unit disjoint-union alpha is starValues(card(alpha),kind). A Schur-complement determinant identity proves the arrow characteristic polynomial; polynomial cancellation is restricted to positive leaf count. Zero leaves are treated directly. Characteristic roots are identified with the actual Hermitian eigenvalues. These star spectra are known suppliers in Das-Erfanian-Nath, rather than a claim of new literature novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.arrowMatrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.starValues`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_matrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.star_spectrum`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](CyclicExtensionRefutation.md)
