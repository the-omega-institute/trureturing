# The permutohedron face lattice

## Abstract

The permutohedron face lattice.

**Definition 1.1 (Cut chains).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.CutChain`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.CutChain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A cut chain on n labels is a finite set of subsets of Fin n. Each cut has cardinality strictly between zero and n, and every two cuts are comparable by inclusion.

**Theorem 1.2 (Equality of cut chains).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.ext_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.ext_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Two cut chains on the same labels are equal if their sets of cuts are equal.

**Definition 1.3 (Faces).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.Face`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.Face` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Face n is the type obtained by adjoining a bottom element to the cut chains on Fin n. The order on chains is reverse inclusion of their cut sets.

**Definition 1.4 (Binary join operation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Intersect the cut sets of two chains. If either input is bottom, return the other input.

**Theorem 1.5 (Join).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For any two faces, their binary join is the least upper bound of the pair.

**Definition 1.6 (Compatible cut chains).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.compatible`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Two cut chains are compatible if every two cuts in the union of their cut sets are comparable by inclusion.

**Definition 1.7 (Binary meet operation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Take the union of the cuts of two compatible chains. Return bottom if either input is bottom or the chains are incompatible.

**Theorem 1.8 (Meet).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

For any two faces, their binary meet is the greatest lower bound of the pair.

**Definition 1.9 (Permutation flags).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.flag`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.flag` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The flag of a permutation of Fin n is the cut chain consisting of its unordered prefixes at all ranks strictly between zero and n.

**Theorem 1.10 (A cut is determined by its size within a chain).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.eq_of_card_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.eq_of_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Two cuts belonging to the same chain are equal if their cardinalities agree.

**Theorem 1.11 (Flag membership at a cut's rank).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.mem_flag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.mem_flag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

A subset with cardinality strictly between zero and n belongs to a permutation flag exactly when the prefix of that cardinality equals the subset.

**Theorem 1.12 (Proper prefixes belong to their flags).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.prefix_mem_flag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.prefix_mem_flag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

At every rank strictly between zero and n, the prefix of a permutation is a cut of its flag.

**Definition 1.13 (The face of a permutation flag).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

View the flag of a permutation as a face via the inclusion of cut chains into Face n.

**Theorem 1.14 (Permutation faces are atoms).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom_isAtom`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom_isAtom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The face of each permutation flag is an atom. Any chain below it would contain the flag and can add no cut, since the flag already has a cut at every proper rank.

**Definition 1.15 (Face rank).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.rank`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.rank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

The integer rank is minus one at bottom and n minus one minus the number of cuts at a chain on n labels.

**Theorem 1.16 (Recognizing a finite join).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.join_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.join_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Suppose a finite family contains a face above bottom. If a chain contains precisely the cuts shared by every chain in the family, then that chain is the finite join of the family.

**Theorem 1.17 (Finite joins).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

When a finite join is a cut chain, a cut belongs to that chain exactly when it belongs to every member that lies above bottom. The empty join is bottom, whose rank is minus one.

**Theorem 1.18 (An extra common cut forces strict inequality).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.strict_of_extra_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.strict_of_extra_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Suppose the join of a finite family is at most a chain x. If some cut is absent from x and belongs to every chain in the family, the join lies strictly below x.

**Theorem 1.19 (Strict inequality for proper subfamilies).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.proper_lt_of_erase_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.proper_lt_of_erase_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

In a join-semilattice with bottom and decidable equality, let A be a finite set. If deleting any one member of A gives a join strictly below x, every proper subset of A has join strictly below x.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.CutChain`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.Face`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.atom_isAtom`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.compatible`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.eq_of_card_eq`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.ext_cuts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceInf_glb`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.faceSup_lub`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.flag`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.join_eq`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.mem_flag`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.prefix_mem_flag`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.proper_lt_of_erase_lt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.rank`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.strict_of_extra_cut`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/FaceLattice.sup_cuts`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension](../../Graph/PrefixHamming/ExactDimension.md)
