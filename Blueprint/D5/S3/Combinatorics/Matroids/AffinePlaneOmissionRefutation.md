# The Affine-Plane Omission Obstruction

## Abstract

The rank-three affine lines can impose dependent restrictions on circuit lifting.

**Definition 1.1 (Independent replacement for the affine lines).**

Lean statement: `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the nine points of the affine plane of order three with singleton parallel classes. For the rank-three matroid whose bases are precisely the triples other than the twelve affine lines, the proposed formula gives nine cyclic factors of order nine.

**Theorem 1.2 (Dependent restrictions in rank three).**

Lean statement: `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twelve omitted lines meet in at most one point per pair and have empty total intersection. A finite coefficient certificate gives eleven vectors over the field of order three. The signed deletion and extension rows vanish on each vector. Eleven basis coordinates recover the independent parameters, so the integral lifting obstruction has at least three to the eleventh elements killed by three, whereas the proposed product has only three to the ninth.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AffinePlaneOmissionRefutation.result`
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
