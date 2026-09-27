# Nikandish's subspace orthogonality clique number

## Abstract

The exact clique number for all nonzero binary subspaces in every positive dimension.

**Definition 1.1 (The source graph).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/NikandishClique.orthogonalityGraph`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/NikandishClique.orthogonalityGraph` (`✓ std3`).

*Citation.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

Vertices are all nonzero subspaces of F_2^n. Distinct U and W are adjacent exactly when sum_i u_i w_i is zero for every u in U and w in W. There is no dimension, nondegeneracy, or intersection restriction.

**Definition 1.2 (An independent lattice count).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/NikandishClique.nonzeroSubspaceCount`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/NikandishClique.nonzeroSubspaceCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

N(r) is the natural cardinality of the complete nonzero submodule lattice of Fin r -> ZMod 2. In particular N(0)=0. No Gaussian-binomial bridge is asserted by this definition or by the result.

**Theorem 1.3 (The exact formula in every dimension).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/NikandishClique.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/NikandishClique.result` (`✓ std3`). ∎

*Resolves.* `Problems/nikandish-subspace-orthogonality-clique` (proved) by `D5/S3/Combinatorics/Orthogonality/NikandishClique.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nikandish-subspace-orthogonality-clique","declaration_gid":"D5/S3/Combinatorics/Orthogonality/NikandishClique.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

For every natural n with 1 <= n, omega(O_n*) equals max(n, N(n/2) + n%2), using natural-number division and remainder. This is the literal all-subspace question in source Problem 4.2.

For an arbitrary clique, sum the radicals of its members to obtain R. Every member U lies in R-perp and U intersect R equals rad(U). The restricted form descends to R-perp/R. Its nonzero member images have nondegenerate restrictions and are indexed independent, so their number is at most n-2 dim(R). The other members inject into the nonzero submodule lattice of R. No nonalternating hypothesis is imposed on the quotient.

For r >= 1, a hyperplane embedding, one outside line, and the whole space give N(r+1) >= N(r)+2. This moves the upper bound to an endpoint. Coordinate lines attain n. Duplicating t coordinates gives a totally isotropic t-space whose full nonzero lattice attains N(t); in odd dimension its perpendicular space is a distinct extra vertex.

The source already provides the odd construction at n=7. Its Lemma 3.2 incorrectly counts three nonzero subspaces of F_2^2; there are four. The present upper bound does not use that argument. Prior-resolution searches are bounded and do not certify worldwide novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NikandishClique.nonzeroSubspaceCount`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NikandishClique.orthogonalityGraph`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NikandishClique.result`
- Dependency: [D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality](../../Fourier/CharacterSelection/BinaryCharacterCodeDuality.md)
