# Irredundant atom sizes of a permutohedron face

## Abstract

The irredundant atom sizes of a face of rank at least two form the interval from two to its rank.

**Theorem 1.1 (Exact spectrum).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow \left(\forall x \in \mathrm{Face}\left(n\right),\; 2 \le \mathrm{rank}\left(x\right) \Rightarrow \left(\forall k \in \mathbb{N},\; (\exists A \in \mathrm{Finset}\left(\mathrm{Face}\left(n\right)\right),\; \mathrm{card}\left(A\right) = k \land \left((\forall a \in \mathrm{Face}\left(n\right),\; a \in A \Rightarrow \mathrm{IsAtom}\left(a\right)) \land \left(\mathrm{sup}\left(A\right) = x \land (\forall B \in \mathrm{Finset}\left(\mathrm{Face}\left(n\right)\right),\; B \subset A \Rightarrow \mathrm{sup}\left(B\right) < x)\right)\right)) \Leftrightarrow (2 \le k \land \mathrm{int}\left(k\right) \le \mathrm{rank}\left(x\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum` (`✓ std3`). ∎

*Resolves.* `Problems/rossi-2026-irredundant-atom-sizes` (proved) by `D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rossi-2026-irredundant-atom-sizes","declaration_gid":"D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Rossi asks in Section 10.3, item 4 which sizes between two and the rank occur for minimal sets of atoms generating a face. Proposition 5.5 of the paper determines the extremal sizes. The grouped exchanges below give the full interval.

A finite family has distinct members and its join is the lattice supremum, with the empty join equal to bottom. Irredundancy requires the join of every proper subfamily to be strictly below the face. The upper bound uses the integer value of the natural size k.

Extend the face to a permutation flag. Partition the free prefix ranks into k nonempty groups, and exchange adjacent positions at the ranks of each group to produce one atom. The common cuts recover the face. Each group has a prefix cut that returns upon removing its atom, so every proper subfamily has strictly smaller join.

For the upper bound, delete one atom at a time and select a cut gained by that deletion. When there are at least three atoms, these cuts have distinct free ranks. The cases of zero, one and two atoms use the bottom, atom and rank conditions directly.

The separate question about covering all atoms below the face remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags](FaceFlags.md)
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges](PrefixExchanges.md)
