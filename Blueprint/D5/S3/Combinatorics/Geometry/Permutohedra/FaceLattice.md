# The permutohedron face lattice

## Abstract

The permutohedron face lattice.

**Theorem 1.1 (Join).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A cut is a proper nonempty subset of the labels. A cut chain is a family of cuts totally ordered by inclusion. Faces order these chains by reverse inclusion, with a bottom below every chain. The least upper bound of two chains consists of their common cuts. Joining with bottom leaves the other face.

**Theorem 1.2 (Meet).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The greatest lower bound of two chains is the union of their cuts when the union is a chain. Otherwise it is bottom. The meet with bottom is bottom.

**Theorem 1.3 (Finite joins).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

When a finite join is a cut chain, a cut belongs to that chain exactly when it belongs to every member that lies above bottom. The empty join is bottom, whose rank is minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension](../../Graph/PrefixHamming/ExactDimension.md)
