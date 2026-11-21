# The affine symmetry group in the original coordinates

## Abstract

The dihedral permutohedron has a full real affine symmetry for each permutation of paper labels and common sign.

**Definition 1.1 (Intrinsic affine stabilizer).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.affineStabilizer`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.affineStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For a set in a real affine space, take the subgroup of all real affine bijections whose image of that set is the set itself.

**Definition 1.2 (The sign group).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.Signs`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.Signs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Use the real units whose square is one, with multiplication.

**Definition 1.3 (Sign as a real number).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.signScalar`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.signScalar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

A sign acts by its underlying real number.

**Definition 1.4 (The negative sign).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.negativeSign`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.negativeSign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Take minus one as an element of the sign group.

**Definition 1.5 (The intrinsic hyperplane).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourcePlane`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourcePlane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n, translate the real sum-zero direction through the constant vector with entry (n + 1) / 2.

**Definition 1.6 (The intrinsic center).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceCenter`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceCenter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n regard the constant source center as a point of the intrinsic hyperplane.

**Definition 1.7 (The hull in the intrinsic plane).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceHull`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceHull` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n take the points of that hyperplane whose ambient vector belongs to the original dihedral orbit hull.

**Definition 1.8 (Rotation with its paper label).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceR`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n and a literal label from 1 through n, regard the corresponding rotation as a point of the intrinsic hyperplane.

**Definition 1.9 (Antipode with its paper label).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceF`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For positive n and a literal label from 1 through n, regard the corresponding antipode as a point of the intrinsic hyperplane.

**Definition 1.10 (The group isomorphism).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceStabilizerEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceStabilizerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For each natural n at least three, this multiplicative equivalence sends a permutation of the one-based paper labels and a common sign to the real affine preserver. The cyclic-difference chart conjugates the action to relabeling the wrap indices and multiplying by that sign.

**Theorem 1.11 (Full real affine symmetry group).**

$$\forall n\geq3:\quad\Vert\operatorname{AffSym}(Q_{n})\Vert=2n!$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For every natural n at least three, the affine hull of the original orbit hull is exactly the real hyperplane with coordinate sum n(n + 1) / 2. The intrinsic vertices indexed by each paper label are the original rotation and antipode with that label.

For every permutation σ of the labels 1 through n and every sign ε, the affine symmetry sends each rotation r_j to c + ε(r_{σ(j)} − c) and each antipode f_j to c + ε(f_{σ(j)} − c). The rotation formulas alone characterize a unique affine symmetry for each pair. Conversely, each affine preserver has a unique such pair.

All preservers fix the center c. Composition is permutation composition and sign multiplication in the same order. The identity permutation with sign minus one is x ↦ 2c − x. The stabilizer has exactly 2n! elements.

The wrap vectors span the sum-zero space, and their only dependence has all coefficients equal. Their signed hull has exactly those signed vertices and has centroid zero. An affine preserver fixes the centroid and permutes the antipodal pairs. The unique dependence forces a common sign across the pairs. The cyclic-difference equivalence carries this action back to the original labels. The result concerns the intrinsic real affine group of the standard-basepoint orbit. The lattice and arbitrary-basepoint questions have separate hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.Signs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.affineStabilizer`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.negativeSign`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.result`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.signScalar`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceCenter`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceF`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceHull`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourcePlane`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceR`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.sourceStabilizerEquiv`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62](OlairezQ62.md)
