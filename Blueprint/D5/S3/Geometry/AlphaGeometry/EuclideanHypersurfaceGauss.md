# EuclideanHypersurfaceGauss

## Abstract

Coordinate Gauss tensor and its scalar trace contraction.

**Definition 1.1 (christoffel).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (k i j : \operatorname{Fin} m) , \operatorname{christoffel} g x k i j = (1 / 2 : \mathbb{R}) * \sum l , (g x) ^{-1} k l * (\operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t l j) x (\operatorname{Pi} . \operatorname{single} i 1) + \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t l i) x (\operatorname{Pi} . \operatorname{single} j 1) - \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t i j) x (\operatorname{Pi} . \operatorname{single} l 1))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.christoffel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of christoffel.

**Definition 1.2 (ricci).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (i j : \operatorname{Fin} m) , \operatorname{ricci} g x i j = \sum k , (\operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t k i j) x (\operatorname{Pi} . \operatorname{single} k 1) - \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t k i k) x (\operatorname{Pi} . \operatorname{single} j 1) + \sum l , (\operatorname{christoffel} g x k k l * \operatorname{christoffel} g x l i j - \operatorname{christoffel} g x k j l * \operatorname{christoffel} g x l i k))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.ricci` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of ricci.

**Definition 1.3 (scalarCurvature).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) , \operatorname{scalarCurvature} g x = \sum i , \sum j , (g x) ^{-1} i j * \operatorname{ricci} g x i j$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.scalarCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of scalarCurvature.

**Theorem 1.4 (coordinate_gauss_scalar_of_ricci).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (b : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) , ((g x) . \operatorname{IsSymm}) \to ((\operatorname{Matrix} . \operatorname{of} (\operatorname{fun} i j \mapsto \operatorname{ricci} g x i j)) = ((g x) ^{-1} * b) . \operatorname{trace} \cdot b - b * (g x) ^{-1} * b) \to \operatorname{scalarCurvature} g x = ((g x) ^{-1} * b) . \operatorname{trace} ^{2} - (((g x) ^{-1} * b) ^{2}) . \operatorname{trace}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.coordinate_gauss_scalar_of_ricci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.5 (structureRHS).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (e : \operatorname{Fin} m \to (\operatorname{Fin} m \to \mathbb{R}) \to E) (N : (\operatorname{Fin} m \to \mathbb{R}) \to E) (\Gamma : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (b : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (i j : \operatorname{Fin} m) (t : (\operatorname{Fin} m \to \mathbb{R})) , \operatorname{structureRHS} e N \Gamma b i j t = (\sum l , \Gamma t l i j \cdot e l t) + b t i j \cdot N t$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.structureRHS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of structureRHS.

**Theorem 1.6 (ricci_of_structure).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (e : \operatorname{Fin} m \to (\operatorname{Fin} m \to \mathbb{R}) \to E) (N : (\operatorname{Fin} m \to \mathbb{R}) \to E) (b : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (x : (\operatorname{Fin} m \to \mathbb{R})) (a : \operatorname{Fin} m \to E \to_{L} [ \mathbb{R} ] \mathbb{R}) (i j : \operatorname{Fin} m) , (\forall l , \operatorname{DifferentiableAt} \mathbb{R} (e l) x) \to (\operatorname{DifferentiableAt} \mathbb{R} N x) \to (\forall l i j , \operatorname{DifferentiableAt} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t l i j) x) \to (\forall i j , \operatorname{DifferentiableAt} \mathbb{R} (\operatorname{fun} t \mapsto b t i j) x) \to (\forall k l , a k (e l x) = \operatorname{if} k = l \operatorname{then} 1 \operatorname{else} 0) \to (\forall k , a k (N x) = 0) \to (\forall i j , (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} j 1)) =^{f} [ \operatorname{nhds} x ] \operatorname{structureRHS} e N (\operatorname{christoffel} g) b i j) \to (\forall i j k , \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} j 1)) x (\operatorname{Pi} . \operatorname{single} k 1) = \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} k 1)) x (\operatorname{Pi} . \operatorname{single} j 1)) \to (\forall k i j , \operatorname{christoffel} g x k i j = \operatorname{christoffel} g x k j i) \to (\forall k j , a k (\operatorname{fderiv} \mathbb{R} N x (\operatorname{Pi} . \operatorname{single} j 1)) = - \sum l , (g x) ^{-1} k l * b x j l) \to \operatorname{ricci} g x i j = b x i j * (\sum k , \sum l , (g x) ^{-1} k l * b x k l) - \sum k , \sum l , b x i k * (g x) ^{-1} k l * b x j l$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.ricci_of_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.7 (inverse_entry_contDiffAt).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (g : E \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : E) (i j : \operatorname{Fin} m) , (\forall i j , \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) (\operatorname{fun} t \mapsto g t i j) x) \to ((g x) . \operatorname{det} \neq 0) \to \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) (\operatorname{fun} t \mapsto (g t) ^{-1} i j) x$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.inverse_entry_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.christoffel`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.coordinate_gauss_scalar_of_ricci`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.inverse_entry_contDiffAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.ricci`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.ricci_of_structure`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.scalarCurvature`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/EuclideanHypersurfaceGauss.structureRHS`
