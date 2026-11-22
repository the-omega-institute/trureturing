# Permutation flags and free ranks

## Abstract

Permutation flags and free ranks.

**Theorem 1.1 (Extending a chain).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Sort the labels by the number of cuts they lie outside, breaking ties by label. Every cut is an initial segment of the resulting permutation.

**Theorem 1.2 (Atoms).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A face is an atom exactly when it is the full chain of proper prefixes of a permutation. Each full chain has one cut at every proper rank, so it has no proper extension as a chain.

**Theorem 1.3 (Free ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For a positive number of labels, the number of proper ranks without a cut equals the rank of the face. The sizes of the cuts of a chain are distinct.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice](FaceLattice.md)
