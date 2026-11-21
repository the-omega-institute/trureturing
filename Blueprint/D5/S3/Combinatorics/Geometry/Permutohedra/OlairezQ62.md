# Cyclic differences in Olairez’s coordinates

## Abstract

Forward cyclic differences identify the dihedral permutohedron with a signed simplex hull.

**Definition 1.1 (Real coordinates).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Coordinates`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For a natural n, the points are real vectors indexed by residues modulo n.

**Definition 1.2 (One-based labels).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabel`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabel` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Subtract one modulo n, take the natural representative, then add one. For positive n this writes the zero residue as the label n.

**Definition 1.3 (Paper label set).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.PaperLabels`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.PaperLabels` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For a natural n, the labels are the natural integers from 1 through n.

**Definition 1.4 (Labels and residues).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabelsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabelsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n, the equivalence sends a residue to its one-based label and sends a label to its residue.

**Definition 1.5 (Cyclic shifts).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.shift`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For any residue a, this permutation adds a to the coordinate index. Its inverse subtracts a.

**Definition 1.6 (Cyclic reflections).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.reflection`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.reflection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For a residue a, this involution sends the index i to a minus i.

**Definition 1.7 (First generator).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s1`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s1` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The first source permutation is index reflection with parameter 3.

**Definition 1.8 (Second generator).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s2`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s2` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The second source permutation is index reflection with parameter 2.

**Definition 1.9 (Dihedral action group).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sourceGroup`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sourceGroup` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The subgroup of coordinate permutations is generated by the two source involutions.

**Definition 1.10 (Inverse-index action).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.act`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.act` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

A coordinate permutation g acts on a vector x by assigning to coordinate i the entry of x at the inverse image of i under g.

**Definition 1.11 (Source matrix convention).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.permutationMatrix`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.permutationMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

At row i and column j the entry is one when g sends j to i, and zero otherwise.

**Definition 1.12 (First generator row).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn1`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn1` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For natural n and one-based row i, the nonzero column is 2 in row 1, 1 in row 2, and n + 3 minus i in the other rows.

**Definition 1.13 (Second generator row).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn2`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn2` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For natural n and one-based row i, the nonzero column is 1 in row 1 and n + 2 minus i in the other rows.

**Definition 1.14 (Standard basepoint).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rho`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rho` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

At coordinate i the vector has value equal to the one-based label of i.

**Definition 1.15 (Center in source coordinates).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.center`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.center` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For each natural n the vector is constant with entry (n + 1) / 2.

**Definition 1.16 (Source rotation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.r`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.r` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The vertex with residue label j has entry at coordinate i equal to the basepoint at residue i + j minus 1.

**Definition 1.17 (Source antipode).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.f`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.f` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For residue label j, each entry is n + 1 minus the corresponding entry of the rotation vertex with that label.

**Definition 1.18 (Actual source orbit).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.orbit`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.orbit` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Take the set of images of the standard basepoint under the dihedral action group.

**Definition 1.19 (Sum-zero direction).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sumZero`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sumZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n this subspace consists of real vectors whose entries sum to zero.

**Definition 1.20 (Centered rotation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rCentered`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rCentered` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n subtract the center from the rotation vector and view the result in the sum-zero space.

**Definition 1.21 (Centered antipode).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.fCentered`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.fCentered` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n subtract the center from the antipodal vector and view the result in the sum-zero space.

**Definition 1.22 (Forward cyclic difference).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.forwardDifference`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.forwardDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n the sum-zero linear map sends a vector to its next coordinate minus its current coordinate, wrapping at the end.

**Definition 1.23 (Cyclic-difference equivalence).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.delta`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n take the linear equivalence on the sum-zero space whose forward map is the forward cyclic difference.

**Definition 1.24 (Coordinate basis vector).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.basisVector`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.basisVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

At residue k the coordinate vector is one, and at all other residues it is zero.

**Definition 1.25 (Cyclic wrap vector).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.wrapPoint`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.wrapPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n and residue k this is the sum-zero vector of ones minus n times the coordinate vector at k.

**Definition 1.26 (Centered orbit).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredOrbit`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n take the vectors in the sum-zero space that arise by subtracting the center from a point of the actual orbit.

**Definition 1.27 (Source polytope).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Q`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Q` (`✓ std3`).

*Citation.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Take the real convex hull of the orbit under the two source permutation generators.

**Definition 1.28 (Centered polytope).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredQ`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n this is the real convex hull of the centered orbit in the sum-zero space.

**Definition 1.29 (Signed wrap vertices).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.signedPoints`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.signedPoints` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n take every wrap vector and its negative.

**Theorem 1.30 (Conjugacy of the original orbit).**

$$\forall n\geq3,\quad\forall j\in\mathbb{Z}_{n}:\quad\Delta(r_{j}-c)=w_{1-j},\quad\Delta(f_{j}-c)=-w_{1-j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.source_coordinate_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Fix any natural n at least three. Residue zero has label n. The generators’ matrix entries are the row-column formulas from Eq. (2). Matrix-vector multiplication equals the inverse-index action, which respects identity and composition. The generators square to the identity and group membership is equivalent to being a shift or a reflection.

The rotation word and the word obtained by appending the fixed reflection send the standard basepoint to the two stated vertex families. Every coordinate of each family follows the formulas for r and f. That fixed reflection sends rotation j to antipode 2 minus j. Using the forward index in place of the inverse fails for the second rotation, and no fixed source reflection pairs each rotation with its own indexed antipode.

The orbit equals the union of both families. Embedding the centered hull into ambient coordinates gives exactly the translate of the source hull by the negative center. The linear equivalence takes forward cyclic differences at every index. Here w_k is the vector of ones minus n times the kth coordinate vector. As j ranges over all residues, 1 minus j ranges over every wrap index. The image of the centered hull is the convex hull of all wrap vectors and their negatives.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Coordinates`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.PaperLabels`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.Q`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.act`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.basisVector`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredOrbit`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.centeredQ`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.delta`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.f`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.fCentered`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.forwardDifference`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.orbit`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn1`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperColumn2`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabel`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.paperLabelsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.permutationMatrix`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.r`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rCentered`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.reflection`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.rho`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s1`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.s2`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.shift`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.signedPoints`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sourceGroup`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.source_coordinate_conjugacy`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.sumZero`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62.wrapPoint`
- Dependency: [D5/S3/Arith/Primes/CyclicDifferencePrimeContent](../../../Arith/Primes/CyclicDifferencePrimeContent.md)
