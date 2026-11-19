# The octahedron diameter-plus-square inequality is false

## Abstract

Two orthogonal octahedral shadows refute the diameter-plus-square scalar bound.

**Definition 1.1 (Orthonormal-row projection matrices).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right),\; (\operatorname{IsProjection}\left(M\right)) \Leftrightarrow (M \cdot \operatorname{Matrix.transpose}\left(M\right) = 1)$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.IsProjection` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 2 states: “Any such orthogonal projection can be written as M · O, for some matrix M ∈ ℝ²ˣ³ satisfying MMᵀ = Id ∈ ℝ²ˣ², and writing M · P ≔ {MP : P ∈ P}.” Fin 2 and Fin 3 index the planar and spatial coordinates starting at zero.

**Definition 1.2 (Filled Euclidean shadows).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right),\; \operatorname{shadow}\left(M\right) = \operatorname{Set.image}\left((fun x : \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \operatorname{WithLp.toLp}\left(2, \operatorname{Matrix.mulVec}\left(M, \operatorname{WithLp.ofLp}\left(x\right)\right)\right)), \operatorname{D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.crossPolytope}\left(3\right)\right)$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.shadow` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 1 states: “Let O ⊆ ℝ³ be the Octahedron with vertices at (e₁,e₂,e₃,−e₁,−e₂,−e₃), where eᵢ denotes the i-th Cartesian unit vector.” shadow takes the linear image of its filled convex hull. EuclideanSpace supplies the Euclidean norm; WithLp converts between that space and coordinate functions.

**Definition 1.3 (Convex-hull diameter).**

$$\forall P \in \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{diameter}\left(P\right) = \operatorname{Metric.diam}\left(\operatorname{convexHull}\left(\mathbb{R}, P\right)\right)$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.diameter` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 4 defines: “Diam(P) is the diameter of P̅, i.e. the largest distance between two points of P̅,” with P̅ the convex hull of P. Metric.diam is applied to that hull.

**Definition 1.4 (All enclosing square lengths).**

$$\forall P \in \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{enclosingSquareLengths}\left(P\right) = \{l : \mathbb{R} \mid (0 \le l) \land (\exists R \in \operatorname{Matrix.specialOrthogonalGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \exists t \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right),\; \forall p \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right),\; (p \in P) \Rightarrow (\forall i \in \operatorname{Fin}\left(2\right),\; \left|\operatorname{Matrix.mulVec}\left((R : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \operatorname{WithLp.ofLp}\left(p - t\right)\right)\left(i\right)\right| \le \frac{l}{2}))\}$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.enclosingSquareLengths` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 8 reads: “As an application of the above statement, we believe to have found a samurai function, that precisely takes its extremes at the optimal solution of the Octahedron: Define □(𝒫) to be the side length of the smallest square, into which 𝒫 fits, and further define 𝔬(𝒫) ≔ Diam(𝒫)+(23/10)□(𝒫).” The set displayed here allows every planar rotation R and every translation t. Weak enclosing lengths and strict enclosing lengths have the same infimum, because each weak enclosure admits an arbitrarily small positive enlargement.

**Definition 1.5 (Smallest enclosing-square side).**

$$\forall P \in \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{squareSide}\left(P\right) = \operatorname{sInf}\left(\operatorname{enclosingSquareLengths}\left(P\right)\right)$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.squareSide` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 8 reads: “As an application of the above statement, we believe to have found a samurai function, that precisely takes its extremes at the optimal solution of the Octahedron: Define □(𝒫) to be the side length of the smallest square, into which 𝒫 fits, and further define 𝔬(𝒫) ≔ Diam(𝒫)+(23/10)□(𝒫).” The infimum is over the displayed enclosing lengths. On every orthogonal shadow this set is nonempty and bounded below by zero; an enclosing square of side two suffices.

**Definition 1.6 (The proposed scalar).**

$$\forall P \in \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{octahedralScalar}\left(P\right) = \operatorname{diameter}\left(P\right) + \frac{23}{10} \cdot \operatorname{squareSide}\left(P\right)$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.octahedralScalar` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 8 reads: “As an application of the above statement, we believe to have found a samurai function, that precisely takes its extremes at the optimal solution of the Octahedron: Define □(𝒫) to be the side length of the smallest square, into which 𝒫 fits, and further define 𝔬(𝒫) ≔ Diam(𝒫)+(23/10)□(𝒫).” The coefficient is the fixed real number 23/10.

**Definition 1.7 (The complete set of projection values).**

$$projectionValues = \{r : \mathbb{R} \mid \exists M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right),\; (\operatorname{IsProjection}\left(M\right)) \land (r = \operatorname{octahedralScalar}\left(\operatorname{shadow}\left(M\right)\right))\}$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.projectionValues` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

The supremum and infimum on printed page 8 range over every orthogonal projection. This set uses all real 2-by-3 matrices satisfying MMᵀ = 1, with no restriction to the two projections used in the counterexample.

**Definition 1.8 (The unnumbered scalar conjecture).**

$$(claim) \Leftrightarrow (\operatorname{sSup}\left(projectionValues\right) \le \frac{3 \cdot \operatorname{Real.sqrt}\left(2\right)}{4} \cdot \operatorname{sInf}\left(projectionValues\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.claim` (`✓ std3`).

*Citation.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

Printed page 8, section 3, states: “We conjecture that any projection of the Octahedron satisfies supπ 𝔬(π(𝐎)) ≤ (3√2/4) infπ 𝔬(π(𝐎)), which would yield another proof of the Nieuwland number of the Octahedron.” projectionValues encodes its complete projection range; sSup and sInf are real extrema.

**Theorem 1.9 (Refutation by a hexagonal shadow).**

$$\neg (\operatorname{sSup}\left(projectionValues\right) \le \frac{3 \cdot \operatorname{Real.sqrt}\left(2\right)}{4} \cdot \operatorname{sInf}\left(projectionValues\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-sy2609oct` (refuted) by `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-sy2609oct","declaration_gid":"D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jakob Steininger and Sergey Yurkevich (2026). *The Nieuwland number of the Octahedron*. DOI: [10.48550/arXiv.2609.10788](https://doi.org/10.48550/arXiv.2609.10788). URL: <https://arxiv.org/abs/2609.10788v1>.

*Commentary.*

The two orthonormal-row matrices yield diameters 2√6/3 and 4√2/3, and smallest enclosing-square sides 1+√3/3 and 4/3. Antipodal vertices remove translations; unit-circle strip inequalities bound all rotations of the hexagonal shadow. The first scalar value exceeds (3√2/4) times the second by more than 9/1250. All projection scalar values lie between zero and nine, so the supremum and infimum are finite and the displayed inequality fails. The Nieuwland-number theorem is a separate assertion.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.IsProjection`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.claim`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.diameter`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.enclosingSquareLengths`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.octahedralScalar`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.projectionValues`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.shadow`
- Truth anchor: `D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.squareSide`
- Dependency: [D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts](../../Combinatorics/Geometry/CrossPolytopeFaceCounts.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope](../../Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.md)
