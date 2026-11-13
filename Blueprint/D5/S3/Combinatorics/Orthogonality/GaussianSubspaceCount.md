# Counting subspaces by their ordered frames

## Abstract

The Gaussian-binomial bridge for the complete binary submodule lattice.

**Definition 1.1 (The product formula).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.gaussian`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.gaussian` (`✓ std3`).

*Citation.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

The coefficient [n choose d]_2 is the product of (2^n-2^i), for 0<=i<d, divided by the product of (2^d-2^i). This is defined arithmetically, independently of the subspace count.

**Theorem 1.2 (Each dimension).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.dimension_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.dimension_card` (`✓ std3`). ∎

*Citation.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

For every 0<=d<=n, the number of actual d-dimensional Submodule (ZMod 2) (Fin n -> ZMod 2) objects equals this coefficient. An independent d-frame has a unique actual span. Conversely each such subspace contributes all of its ordered bases. The explicit sigma equivalence partitions the frames by their span; Mathlib's finite-frame formula counts the ambient frames and each basis fiber. The basis factor is positive, including the empty product at d=0.

**Theorem 1.3 (All nonzero subspaces).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.result` (`✓ std3`). ∎

*Citation.* R. Nikandish (2026). *Annihilating-Ideal Graphs and Orthogonality Graphs over F_2*. DOI: [10.48550/arXiv.2609.22769](https://doi.org/10.48550/arXiv.2609.22769). URL: <https://arxiv.org/abs/2609.22769v1>.

*Commentary.*

For every n, NikandishClique.nonzeroSubspaceCount n equals the sum of [n choose d]_2 over 1<=d<=n. A second explicit sigma equivalence partitions every nonzero submodule by its finrank; zero rank is equivalent to the zero submodule. Thus the empty n=0 sum is zero. Combined with the existing clique result this supplies its displayed Gaussian-binomial formula without re-proving the radical-quotient argument. The proofs are independently written from the standard frame-count argument and the source's full lattice domain.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.dimension_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.gaussian`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount.result`
- Dependency: [D5/S3/Combinatorics/Orthogonality/NikandishClique](NikandishClique.md)
