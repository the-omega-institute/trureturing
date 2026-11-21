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

$$\begin{aligned}&\forall n \in \mathbb{N}, n\geq3 \implies\\&(\operatorname{aff}_{\mathbb{R}}\left(Q_{n}\right)=P_{n}\\&\land (\forall x \in V_{n}, x \in P_{n} \iff \sum_{i \in \mathbb{Z}_{n}}x_{i}=\frac{n(n+1)}{2})\\&\land (\forall a \in L_{n}, \iota\left(R_{a}\right)=r_{\overline{a}} \land \iota\left(F_{a}\right)=f_{\overline{a}})\\&\land (\forall (\sigma,\varepsilon) \in \operatorname{Sym}\left(L_{n}\right) \times \{1, -1\}, \forall a \in L_{n}, \iota\left(\phi_{(\sigma,\varepsilon)}\left(R_{a}\right)\right)=c+\varepsilon \cdot (\iota\left(R_{\sigma\left(a\right)}\right)-c)\\&\quad\land \iota\left(\phi_{(\sigma,\varepsilon)}\left(F_{a}\right)\right)=c+\varepsilon \cdot (\iota\left(F_{\sigma\left(a\right)}\right)-c))\\&\land (\forall (\sigma,\varepsilon) \in \operatorname{Sym}\left(L_{n}\right) \times \{1, -1\}, \exists! T \in A_{n}, \forall a \in L_{n}, \iota\left(T\left(R_{a}\right)\right)=c+\varepsilon \cdot (\iota\left(R_{\sigma\left(a\right)}\right)-c))\\&\land (\forall T \in A_{n}, \exists! (\sigma,\varepsilon) \in \operatorname{Sym}\left(L_{n}\right) \times \{1, -1\}, \forall a \in L_{n}, \iota\left(T\left(R_{a}\right)\right)=c+\varepsilon \cdot (\iota\left(R_{\sigma\left(a\right)}\right)-c))\\&\land (\forall T \in A_{n}, T\left(C\right)=C)\\&\land (\forall (\sigma,\varepsilon),(\tau,\alpha) \in \operatorname{Sym}\left(L_{n}\right) \times \{1, -1\}, \forall x \in P_{n}, \phi_{(\sigma \circ \tau,\varepsilon\alpha)}\left(x\right)=\phi_{(\sigma,\varepsilon)}\left(\phi_{(\tau,\alpha)}\left(x\right)\right))\\&\land (\forall x \in P_{n}, \iota\left(\phi_{(1,-1)}\left(x\right)\right)=2 \cdot c-\iota\left(x\right))\\&\land \operatorname{card}\left(A_{n}\right)=2 \cdot n!)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.result` (`✓ std3`). ∎

*Resolves.* `Problems/olairez-2026-dihedral-permutohedron-affine-symmetries` (proved) by `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"olairez-2026-dihedral-permutohedron-affine-symmetries","declaration_gid":"D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The ambient coordinate space Vₙ is indexed by residues Zₙ, and Pₙ is the intrinsic source plane with inclusion ι into Vₙ. The hull Qₙ is in Vₙ, and Hₙ is its preimage in Pₙ. Write Aₙ for the group of real affine bijections of Pₙ that carry Hₙ onto itself. The ambient center is c and its point in Pₙ is C.

Lₙ consists of the literal paper labels 1 through n. The bar on a label denotes its residue, so label n has residue zero. Rₐ and Fₐ are the intrinsic vertices, and r and f are the original residue-indexed families. The affine map φ for each permutation and sign is the image of that pair under the group equivalence above. The signs in the ambient action formulas act by their real scalars.

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
