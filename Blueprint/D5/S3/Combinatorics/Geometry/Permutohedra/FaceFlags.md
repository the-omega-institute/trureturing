# Permutation flags and free ranks

## Abstract

Permutation flags and free ranks.

**Definition 1.1 (Cuts preceding a label).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.preceding`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.preceding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For a cut chain and a label, keep the cuts of the chain that omit the label.

**Theorem 1.2 (Extending a chain).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Sort the labels by the number of cuts they lie outside, breaking ties by label. Every cut is an initial segment of the resulting permutation.

**Theorem 1.3 (Atoms).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A face is an atom exactly when it is the full chain of proper prefixes of a permutation. Each full chain has one cut at every proper rank, so it has no proper extension as a chain.

**Definition 1.4 (Occupied ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.occupied`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The occupied ranks of a chain are the cardinalities of its cuts, viewed as proper ranks.

**Definition 1.5 (Unoccupied ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.free`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.free` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The free ranks of a chain are the proper ranks outside its occupied set.

**Theorem 1.6 (Number of proper ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_rank_type`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_rank_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For every natural n, the number of ranks strictly between zero and n is n minus one in the natural numbers, with subtraction truncated at zero.

**Theorem 1.7 (Free ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For a positive number of labels, the number of proper ranks without a cut equals the rank of the face. The sizes of the cuts of a chain are distinct.

**Theorem 1.8 (Prefixes at occupied ranks).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.prefix_mem_cuts_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.prefix_mem_cuts_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

If a permutation flag contains all cuts of a chain, the prefix at a proper rank belongs to the chain exactly when that rank is occupied by the chain.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_free`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.card_rank_type`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.exists_flag_extension`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.free`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.isAtom_iff_flag`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.occupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.preceding`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags.prefix_mem_cuts_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice](FaceLattice.md)
