# A perp hyperplane and classical hexagon intersections

## Abstract

The IIZ perp hyperplane refutes the classical-hexagon contextuality generalization.

**Definition 1.1 (Three-qubit binary labels).**

$$\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point} = ((\operatorname{Fin}\left(3\right)) \to ((\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.point` (`✓ std3`).

*Citation.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

A label assigns a pair of binary coordinates to each of three qubits. The pair gives the X and Z exponents, with the pair (1,1) represented by Y = iXZ. The zero label represents the identity and is included in this type. The map in main.tex, lines 213–222, lists the Z coordinates before the X coordinates; here the coordinates are grouped by qubit with X first. The projective points are the nonzero labels, as in lines 222–233.

**Definition 1.2 (The full binary symplectic space).**

$$(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.w}: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)) = (\operatorname{Top.top}: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.w` (`✓ std3`).

*Citation.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

The submodule w is the whole space of three-qubit labels. Its nonzero vectors are the 63 points of W(5,2), and its isotropic triples are the lines. This is the ambient space of main.tex, lines 222–233 and 736–740.

**Definition 1.3 (Additive Pauli product signs).**

$$\forall (l: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.lineSign}\left(l\right): \operatorname{ZMod}\left(2\right)) = \operatorname{ite}\left(\operatorname{D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.lineProduct}\left(l\right) = -(1: \operatorname{Matrix}\left(((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right))), ((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right))), \mathbb{C}\right)), (1: \operatorname{ZMod}\left(2\right)), (0: \operatorname{ZMod}\left(2\right))\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.lineSign` (`✓ std3`).

*Citation.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

The value is one in ZMod 2 when the matrix product of l is minus the identity matrix, and zero otherwise. The definition applies to every finite set of labels; for a line it is the binary valuation of its context sign in main.tex, lines 346–349. The displayed identity is a matrix identity on the three-qubit space, rather than a complex scalar.

**Definition 1.4 (Unsatisfied contexts of an assignment).**

$$\forall (c: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)\right)), (\forall (f: ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}) \to (\operatorname{ZMod}\left(2\right)))), ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.violations}\left(c, f\right): \mathbb{N}) = (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda (l: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)) \mapsto (\operatorname{Finset.sum}\left(l, (\lambda (q: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}) \mapsto (f\left(q\right)))\right) \ne \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.lineSign}\left(l\right))), c\right)\right): \mathbb{N})))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.violations` (`✓ std3`).

*Citation.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

For a binary assignment f, count the members l of c for which the sum of the assigned values differs from the additive Pauli sign. Binary addition encodes multiplication of signs, with zero representing plus one. This is the count of unsatisfied contexts in main.tex, lines 341–355. The cardinality takes values in the natural numbers without a cast.

**Definition 1.5 (Minimum violation count).**

$$\forall (c: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)\right)), ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.contextualityDegree}\left(c\right): \mathbb{N}) = \operatorname{sInf}\left(\operatorname{Set.range}\left((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.violations}\left(c\right): ((((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}) \to (\operatorname{ZMod}\left(2\right)))) \to (\mathbb{N})))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.contextualityDegree` (`✓ std3`).

*Citation.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

Take the natural infimum of the range of violation counts over all binary assignments on the label type. This is a nonempty finite set of attainable counts, so its infimum is its minimum. The value at the zero label has no effect on a family of lines. This expresses the contextuality degree and incidence-matrix Hamming distance of main.tex, lines 341–352.

**Definition 1.6 (The hexagon incidence and planarity conditions).**

$$\forall (h: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)\right)), ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.IsClassicalHexagon}\left(h\right): \operatorname{Prop}) = \left((h \subseteq \operatorname{D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.lines}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.w}\right)) \land ((\forall (q: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), ((q \in \operatorname{D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.points}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.w}\right)) \Rightarrow ((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda (l: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)) \mapsto (q \in l)), h\right)\right): \mathbb{N}) = (3: \mathbb{N})))) \land ((\forall (a: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (b: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (c: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (l: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((l \in h) \Rightarrow (\forall (m: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((m \in h) \Rightarrow (\forall (n: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((n \in h) \Rightarrow ((a \ne b) \Rightarrow ((b \ne c) \Rightarrow ((c \ne a) \Rightarrow ((l \ne m) \Rightarrow ((m \ne n) \Rightarrow ((n \ne l) \Rightarrow ((a \in l) \Rightarrow ((b \in l) \Rightarrow ((b \in m) \Rightarrow ((c \in m) \Rightarrow ((c \in n) \Rightarrow ((a \in n) \Rightarrow (\operatorname{False})))))))))))))))))))))) \land (\forall (z: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (a: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (b: \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}), (\forall (l: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((l \in h) \Rightarrow (\forall (m: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)), ((m \in h) \Rightarrow ((z \in l) \Rightarrow ((z \in m) \Rightarrow ((a \in l) \Rightarrow ((b \in m) \Rightarrow (\operatorname{D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.B}\left(a, b\right) = (0: \operatorname{ZMod}\left(2\right))))))))))))))))\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.IsClassicalHexagon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

The finite family h consists of isotropic lines, with exactly three lines through each nonzero point. Three distinct points cannot be joined cyclically by three distinct lines of h. Whenever two lines of h pass through the same point z, every point a on the first is orthogonal to every point b on the second. These are the incidence, absence-of-triangles and planarity conditions used here. Every classical embedding in main.tex, lines 289–300 and 477–479, satisfies them; the predicate does not assert a characterization of all such embeddings.

**Definition 1.7 (The equality proposed for arbitrary contextual line families).**

$$(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.claim}: \operatorname{Prop}) = (\forall (c: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)\right)), ((c \subseteq \operatorname{D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.lines}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.w}\right)) \Rightarrow (((0: \mathbb{N}) < \operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.contextualityDegree}\left(c\right)) \Rightarrow (\exists (h: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.point}\right)\right)), ((\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.IsClassicalHexagon}\left(h\right)) \land (\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.contextualityDegree}\left(c\right) = (\operatorname{Finset.card}\left(\operatorname{Finset.inter}\left(c, h\right)\right): \mathbb{N})))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

Every finite family c of isotropic lines with positive contextuality degree would have the same degree as the natural number of its lines shared with some h satisfying the hexagon conditions. This is the line-family reading of the generalization in main.tex, lines 736–740. The next paragraph, lines 742–744, includes the complement of a skew hexagon among the subgeometries to which that generalization is applied.

**Theorem 1.8 (The perp hyperplane contradicts the equality).**

$$\neg (\operatorname{D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/saniga-et-al-2025-hexagon-contextuality-generalization` (refuted) by `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"saniga-et-al-2025-hexagon-contextuality-generalization","declaration_gid":"D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Metod Saniga; Frédéric Holweck; Colm Kelleher; Axel Muller; Alain Giorgetti; Henri de Boutray (2025). *Hexagons govern three-qubit contextuality*. DOI: [10.22331/q-2025-01-20-1601](https://doi.org/10.22331/q-2025-01-20-1601). URL: <https://arxiv.org/abs/2312.07738v3>.

*Commentary.*

Let C be the family of all isotropic lines whose points commute with IIZ, and let S be the nonzero labels commuting with IIZ. There are 63 nonzero labels in the whole space and 31 in S. Enumerate the triples generated by distinct orthogonal labels u and v in S for which the sum of the three single-qubit multiplication exponents is two in ZMod 4. There are twelve distinct triples in this enumeration.

Every isotropic line has the form {u,v,u+v} for distinct nonzero orthogonal u and v, and every such set of three points is a line. The multiplication phase of u and v is the additive character of their total multiplication residue in ZMod 4. That character takes the value minus one exactly at two. The product of the three observables is the phase times the identity matrix, so a line of C is negative exactly when it is one of the twelve enumerated triples. Double counting incidences between any line family and any point set equates the sum of intersection sizes over lines with the sum of line degrees over points. Each isotropic line meets S in three points if it belongs to C and in one point otherwise: the binary form on u, v and u+v gives precisely these two possibilities. Applying the incidence identity to all 63 points, with three points per line and three lines through each point, shows that every h satisfying the hexagon conditions has 63 lines.

The six triples {XII,IXI,XXI}, {IZI,ZII,ZZI}, {XZI,ZXI,YYI}, {XII,IZI,XZI}, {IXI,ZII,ZXI} and {XXI,ZZI,YYI} all lie in C. Map the nine row-major labels to the square in RankOfContextualityNonPowerTwo. Convert an assignment value to true exactly when it is one in ZMod 2. The frozen Square.parity_miss gives a context whose Boolean parity differs from its target; Square.bv_parity identifies that parity with the binary sum. The Pauli sign agrees with the target, since only the last context is negative. Thus every assignment violates at least one of these six lines, and the contextuality degree of C is positive. The constant zero assignment violates exactly the twelve negative lines, giving degree at most twelve.

Now count incidences between h and S. Each of the 31 points of S lies on three lines of h, giving 93 incidences. Write k for the natural cardinality of C intersect h. The k lines contained in S contribute three incidences each, while the other 63 minus k lines contribute one each. Hence 93 = 2k + 63, which gives at least fifteen shared lines. Applying the asserted equality to C would identify its degree, at most twelve, with this intersection cardinality, at least fifteen. The resulting natural-number inequalities contradict each other. The argument uses only the line and degree conditions of h, so it also applies when the triangle and planarity conditions are retained.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.IsClassicalHexagon`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.contextualityDegree`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.lineSign`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.point`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.violations`
- Truth anchor: `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.w`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBound](../../Combinatorics/Graph/DominatingSetAverageBound.md)
- Dependency: [D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity](LinearDoilyNegativeLineParity.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
- Dependency: [D5/S3/QuantumContext/RankOfContextualityNonPowerTwo](../../QuantumContext/RankOfContextualityNonPowerTwo.md)
