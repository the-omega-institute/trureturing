# Vicinal width under component cuts

## Abstract

Vicinal width under component cuts.

**Theorem 1.1 (Reversing vicinal order).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.vicinal_compl_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.vicinal_compl_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Complementation exchanges the two vertices in the vicinal comparison.

**Theorem 1.2 (Chain covers of complements).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.hasChainCover_compl_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.hasChainCover_compl_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The same assignment to chain labels works for a graph and its complement.

**Definition 1.3 (Natural width).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

On finite graphs choose the least feasible vicinal chain-cover size.

**Theorem 1.4 (Agreement of the two widths).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.dilworthNumber_eq_width`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.dilworthNumber_eq_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The least natural size equals the extended-natural infimum after casting.

**Theorem 1.5 (Natural width under complement).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

A graph and its complement have the same natural width.

**Theorem 1.6 (Singleton width).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The unique vertex requires and supplies one chain.

**Theorem 1.7 (Width of a component cut).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For a finite nonempty graph, take the maximum of one and the sum of the widths of the nonsingleton components. Isolates can be placed in an existing chain.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.dilworthNumber_eq_width`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.hasChainCover_compl_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.vicinal_compl_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_compl`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_components`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.width_singleton`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation](MandalMannaDQDilworthRefutation.md)
