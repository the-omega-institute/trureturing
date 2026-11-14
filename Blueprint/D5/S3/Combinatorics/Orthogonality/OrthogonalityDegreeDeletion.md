# Subspace degrees and extension of every retained coloring

## Abstract

Exact degrees and reversible deletion in the complete nonzero binary subspace graph.

**Theorem 1.1 (Every contained nonzero subspace).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.below_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.below_card` (`✓ std3`). ∎

*Citation.* Public binary-subspace-orthogonality research workspace; individual derivation attribution unspecified (2026). *Degree and list-color deletion for binary subspace orthogonality*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/manuscript/sections/higher-dimensions.tex>.

*Commentary.*

The original proved subtype map/comap count is exposed for the live six-dimensional label-list consumer. Every nonzero submodule contained in X is counted by N(finrank X); its existing proof body is reused without a second lattice count.

**Theorem 1.2 (Exact degrees).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.degree_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.degree_card` (`✓ std3`). ∎

*Citation.* Public binary-subspace-orthogonality research workspace; individual derivation attribution unspecified (2026). *Degree and list-color deletion for binary subspace orthogonality*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/manuscript/sections/higher-dimensions.tex>.

*Commentary.*

For every natural n and every actual nonzero submodule U of Fin n -> ZMod 2, write d=finrank U and N(r)=NikandishClique.nonzeroSubspaceCount r. The cardinality of U's neighbor set is N(n-d)-1 if U is contained in its orthogonal, and N(n-d) otherwise. The condition is pairwise total isotropy, not merely the existence of a self-isotropic vector.

Nonzero submodules contained in U-perp correspond bijectively to nonzero submodules of U-perp itself, by subtype map and comap. A basis identifies that space with the binary coordinate space of dimension n-d. Finally erase U itself exactly when it is in this lattice. The graph is loopless. No catalogue completeness, Gaussian-binomial formula or finite computation is assumed.

**Theorem 1.3 (Preserve every retained color).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.result` (`✓ std3`). ∎

*Citation.* Public binary-subspace-orthogonality research workspace; individual derivation attribution unspecified (2026). *Degree and list-color deletion for binary subspace orthogonality*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/manuscript/sections/higher-dimensions.tex>.

*Commentary.*

For arbitrary n,k and a finite set D of actual nonzero submodules, assume N(n-dim U)<k for each U in D. Every Fin k coloring of the induced graph outside D extends to the complete orthogonality graph, with exactly the same color at each vertex outside D. Thus restriction and extension give equivalent k-colorability, and a fixed clique disjoint from D keeps all its assigned colors.

Induct on the deleted set. Restore one vertex using a color outside the image of its already colored neighbors. That image has cardinality at most the vertex degree, which is strictly less than k by the exact formula. For a fixed k-clique, f adjacent fixed vertices use f distinct colors; both the residual degree bound and palette size lose these f colors. The inequality N(n-d)<k is therefore sufficient for the source's list deletion rule. The extension theorem preserves all retained colors, including these fixed assignments.

The quantifiers include empty D, dimension zero and an empty palette. If a nonempty D satisfies the strict inequality then k is positive. No n=7 coloring or solver certificate is claimed. Historical k=16 preprocessing counts and later obstructions remain source reports. The exact n=7 chromatic number and the paused 19-color exclusion work remain open and untouched.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.below_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.degree_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.result`
- Dependency: [D5/S3/Combinatorics/Orthogonality/NikandishClique](NikandishClique.md)
