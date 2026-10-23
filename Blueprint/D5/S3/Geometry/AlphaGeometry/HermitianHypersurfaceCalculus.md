# HermitianHypersurfaceCalculus

## Abstract

Hermitian density coordinates and hypersurface calculus with the positive cubic derivative.

**Definition 1.1 (G).**

$$\forall (n : \mathbb{N}), \forall (k : \operatorname{Fin}\left((n^{2}) - (1)\right)), \operatorname{G}\left(n, k\right) = \operatorname{fun} (r : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (s : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{let} row := \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(k\right), n\right); \operatorname{let} col := \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(k\right), n\right); \operatorname{if} (row = col) \operatorname{then} ((\operatorname{if} ((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = row)) \operatorname{then} (1) \operatorname{else} (0)) - (\operatorname{if} ((\operatorname{val}\left(r\right) = (n) - (1)) \land (\operatorname{val}\left(s\right) = (n) - (1))) \operatorname{then} (1) \operatorname{else} (0))) \operatorname{else} (\operatorname{if} (row < col) \operatorname{then} (\operatorname{if} (((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = col)) \lor ((\operatorname{val}\left(r\right) = col) \land (\operatorname{val}\left(s\right) = row))) \operatorname{then} (1) \operatorname{else} (0)) \operatorname{else} ((\operatorname{if} ((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = col)) \operatorname{then} (\operatorname{Complex}.\operatorname{I}) \operatorname{else} (0)) - (\operatorname{if} ((\operatorname{val}\left(r\right) = col) \land (\operatorname{val}\left(s\right) = row)) \operatorname{then} (\operatorname{Complex}.\operatorname{I}) \operatorname{else} (0))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural matrix-grid index omits the last diagonal position. Nat.div and Nat.mod are natural-number division and remainder. Diagonal directions subtract the final diagonal entry; the two ordered off-diagonal positions give the real and imaginary Hermitian directions.

**Definition 1.2 (rho).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{rho}\left(x\right) = (\frac{1}{n : \mathbb{R}}) \cdot (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) + \sum_{k : \operatorname{Fin}\left((n^{2}) - (1)\right)} ((x\left(k\right)) \cdot (\operatorname{G}\left(n, k\right)))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine chart has trace-one center and traceless Hermitian coordinate directions. Scalar multiplication is over the real numbers.

**Definition 1.3 (chartPoint).**

$$\forall (n : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{chartPoint}\left(A\right) = \operatorname{fun} (k : \operatorname{Fin}\left((n^{2}) - (1)\right)) \mapsto \operatorname{let} row := \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(k\right), n\right); \operatorname{let} col := \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(k\right), n\right); \operatorname{if} h : (row < n) \land (col < n) \operatorname{then} (\operatorname{let} entry := A\left(\langle row, h.1\rangle, \langle col, h.2\rangle\right); \operatorname{if} (row = col) \operatorname{then} ((entry.\operatorname{re}) - (\frac{1}{n : \mathbb{R}})) \operatorname{else} (\operatorname{if} (row < col) \operatorname{then} (entry.\operatorname{re}) \operatorname{else} (entry.\operatorname{im}))) \operatorname{else} 0$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.chartPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse chart reads the real upper entries, the imaginary lower entries, and the centered diagonal entries. The bound proof h supplies the two Fin indices. Nat.div and Nat.mod use natural-number division and remainder.

**Theorem 1.4 (rho_isHermitian).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{rho}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every chart value is Hermitian.

**Theorem 1.5 (rho_trace).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{rho}\left(x\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive matrix dimension the chart value has trace one.

**Theorem 1.6 (chart_left_inverse).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{chartPoint}\left(\operatorname{rho}\left(x\right)\right) = x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.chart_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the coordinates of a chart value recovers every original coordinate.

**Theorem 1.7 (hermitian_trace_one_chart_equiv).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(A\right) = 1) \Rightarrow (\operatorname{rho}\left(\operatorname{chartPoint}\left(A\right)\right) = A)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.hermitian_trace_one_chart_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reconstructing a Hermitian trace-one matrix from its chart coordinates recovers the matrix. The final diagonal coordinate follows from the trace equation.

**Theorem 1.8 (hermitian_posdef_open).**

$$\forall (n : \mathbb{N}), \operatorname{IsOpen}\left(\{A : \{A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) // \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)\} \mid \operatorname{Matrix}.\operatorname{PosDef}\left(\operatorname{val}\left(A\right)\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.hermitian_posdef_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definite matrices form an open set in the Hermitian subspace.

**Theorem 1.9 (positive_chart_open).**

$$\forall (n : \mathbb{N}), \operatorname{IsOpen}\left(\{x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R}) \mid \operatorname{Matrix}.\operatorname{PosDef}\left(\operatorname{rho}\left(x\right)\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.positive_chart_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definiteness is an open condition in the density coordinates.

**Definition 1.10 (christoffel).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (k i j : \operatorname{Fin} m) , \operatorname{christoffel} g x k i j = (1 / 2 : \mathbb{R}) * \sum l , (g x) ^{-1} k l * (\operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t l j) x (\operatorname{Pi} . \operatorname{single} i 1) + \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t l i) x (\operatorname{Pi} . \operatorname{single} j 1) - \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto g t i j) x (\operatorname{Pi} . \operatorname{single} l 1))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.christoffel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of christoffel.

**Definition 1.11 (ricci).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (i j : \operatorname{Fin} m) , \operatorname{ricci} g x i j = \sum k , (\operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t k i j) x (\operatorname{Pi} . \operatorname{single} k 1) - \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t k i k) x (\operatorname{Pi} . \operatorname{single} j 1) + \sum l , (\operatorname{christoffel} g x k k l * \operatorname{christoffel} g x l i j - \operatorname{christoffel} g x k j l * \operatorname{christoffel} g x l i k))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.ricci` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of ricci.

**Definition 1.12 (scalarCurvature).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) , \operatorname{scalarCurvature} g x = \sum i , \sum j , (g x) ^{-1} i j * \operatorname{ricci} g x i j$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.scalarCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of scalarCurvature.

**Theorem 1.13 (coordinate_gauss_scalar_of_ricci).**

$$\forall \{ m : \mathbb{N} \} (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : \operatorname{Fin} m \to \mathbb{R}) (b : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) , ((g x) . \operatorname{IsSymm}) \to ((\operatorname{Matrix} . \operatorname{of} (\operatorname{fun} i j \mapsto \operatorname{ricci} g x i j)) = ((g x) ^{-1} * b) . \operatorname{trace} \cdot b - b * (g x) ^{-1} * b) \to \operatorname{scalarCurvature} g x = ((g x) ^{-1} * b) . \operatorname{trace} ^{2} - (((g x) ^{-1} * b) ^{2}) . \operatorname{trace}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.coordinate_gauss_scalar_of_ricci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.14 (structureRHS).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (e : \operatorname{Fin} m \to (\operatorname{Fin} m \to \mathbb{R}) \to E) (N : (\operatorname{Fin} m \to \mathbb{R}) \to E) (\Gamma : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (b : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (i j : \operatorname{Fin} m) (t : (\operatorname{Fin} m \to \mathbb{R})) , \operatorname{structureRHS} e N \Gamma b i j t = (\sum l , \Gamma t l i j \cdot e l t) + b t i j \cdot N t$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.structureRHS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of structureRHS.

**Theorem 1.15 (ricci_of_structure).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (g : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (e : \operatorname{Fin} m \to (\operatorname{Fin} m \to \mathbb{R}) \to E) (N : (\operatorname{Fin} m \to \mathbb{R}) \to E) (b : (\operatorname{Fin} m \to \mathbb{R}) \to \operatorname{Fin} m \to \operatorname{Fin} m \to \mathbb{R}) (x : (\operatorname{Fin} m \to \mathbb{R})) (a : \operatorname{Fin} m \to E \to_{L} [ \mathbb{R} ] \mathbb{R}) (i j : \operatorname{Fin} m) , (\forall l , \operatorname{DifferentiableAt} \mathbb{R} (e l) x) \to (\operatorname{DifferentiableAt} \mathbb{R} N x) \to (\forall l i j , \operatorname{DifferentiableAt} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{christoffel} g t l i j) x) \to (\forall i j , \operatorname{DifferentiableAt} \mathbb{R} (\operatorname{fun} t \mapsto b t i j) x) \to (\forall k l , a k (e l x) = \operatorname{if} k = l \operatorname{then} 1 \operatorname{else} 0) \to (\forall k , a k (N x) = 0) \to (\forall i j , (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} j 1)) =^{f} [ \operatorname{nhds} x ] \operatorname{structureRHS} e N (\operatorname{christoffel} g) b i j) \to (\forall i j k , \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} j 1)) x (\operatorname{Pi} . \operatorname{single} k 1) = \operatorname{fderiv} \mathbb{R} (\operatorname{fun} t \mapsto \operatorname{fderiv} \mathbb{R} (e i) t (\operatorname{Pi} . \operatorname{single} k 1)) x (\operatorname{Pi} . \operatorname{single} j 1)) \to (\forall k i j , \operatorname{christoffel} g x k i j = \operatorname{christoffel} g x k j i) \to (\forall k j , a k (\operatorname{fderiv} \mathbb{R} N x (\operatorname{Pi} . \operatorname{single} j 1)) = - \sum l , (g x) ^{-1} k l * b x j l) \to \operatorname{ricci} g x i j = b x i j * (\sum k , \sum l , (g x) ^{-1} k l * b x k l) - \sum k , \sum l , b x i k * (g x) ^{-1} k l * b x j l$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.ricci_of_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.16 (inverse_entry_contDiffAt).**

$$\forall \{ m : \mathbb{N} \} \{ E : \operatorname{Type} \} [ \operatorname{NormedAddCommGroup} E ] [ \operatorname{NormedSpace} \mathbb{R} E ] (g : E \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{R}) (x : E) (i j : \operatorname{Fin} m) , (\forall i j , \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) (\operatorname{fun} t \mapsto g t i j) x) \to ((g x) . \operatorname{det} \neq 0) \to \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) (\operatorname{fun} t \mapsto (g t) ^{-1} i j) x$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.inverse_entry_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.17 (herm_inner).**

$$\operatorname{fun} \{ n : \mathbb{N} \} (A B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \mapsto \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (A * B))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.herm_inner` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The closed defining function of the real trace pairing on Hermitian matrices. The declaration name is herm_inner; the formula displays its defining expression.

**Definition 1.18 (cubeDerivative).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{cubeDerivative} Y = ((\operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toLinearMap} . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (Y . \operatorname{val} ^{2}) + ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) Y . \operatorname{val}) . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{flip} Y . \operatorname{val}) + (\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{flip} (Y . \operatorname{val} ^{2}))) . \operatorname{comp} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{subtype}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cubeDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of cubeDerivative.

**Theorem 1.19 (positive_hermitian_cube_derivative_equiv).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , (Y . \operatorname{val} . \operatorname{PosDef}) \to \operatorname{Function} . \operatorname{Bijective} (\operatorname{cubeDerivative} Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.positive_hermitian_cube_derivative_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.20 (cubeDerivativeEquiv).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (\operatorname{hY} : Y . \operatorname{val} . \operatorname{PosDef}) (\operatorname{hB} : \operatorname{Function} . \operatorname{Bijective} (\operatorname{cubeDerivative} Y)) , \operatorname{cubeDerivativeEquiv} Y \operatorname{hY} = (\operatorname{LinearEquiv} . \operatorname{ofInjectiveEndo} (\operatorname{cubeDerivative} Y) \operatorname{hB} . 1) . \operatorname{toContinuousLinearEquiv}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cubeDerivativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full equivalence construction from the cubic derivative. The injectivity proof is displayed as a bound proof argument; proof irrelevance identifies it with the established positive-derivative proof.

**Definition 1.21 (cube).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{cube} Y = \operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (Y . \operatorname{val} ^{3})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of cube.

**Theorem 1.22 (cube_val).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (\operatorname{cube} Y) . \operatorname{val} = Y . \operatorname{val} ^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.23 (cube_contDiff).**

$$\forall (n : \mathbb{N}) , \operatorname{ContDiff} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) ((\operatorname{fun} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) \mapsto \operatorname{cube} Y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.24 (cube_hasFDerivAt).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{HasFDerivAt} \operatorname{cube} (\operatorname{cubeDerivative} Y) . \operatorname{toContinuousLinearMap} Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.25 (F).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , F Y = (Y . \operatorname{val} ^{3}) . \operatorname{trace} . \operatorname{re}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of F.

**Definition 1.26 (DF).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{DF} Y = (3 : \mathbb{R}) \cdot (((\operatorname{Complex} . \operatorname{reCLM} . \operatorname{comp} (\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} n) \mathbb{R} \mathbb{C} : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \to_{l} [ \mathbb{R} ] \mathbb{C}) . \operatorname{toContinuousLinearMap})) . \operatorname{comp} (((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toContinuousBilinearMap} (Y . \operatorname{val} ^{2})) . \operatorname{comp} ((\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) . \operatorname{subtypeL}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.DF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of DF.

**Theorem 1.27 (F_hasFDerivAt).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{HasFDerivAt} F (\operatorname{DF} Y) Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.28 (F_fderiv).**

$$\forall \{ n : \mathbb{N} \} (Y V : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{fderiv} \mathbb{R} F Y V = 3 * \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((Y . \operatorname{val} ^{2})) * (V . \operatorname{val})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F_fderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.DF`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F_fderiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.F_hasFDerivAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.G`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.chartPoint`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.chart_left_inverse`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.christoffel`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.coordinate_gauss_scalar_of_ricci`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cubeDerivative`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cubeDerivativeEquiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_contDiff`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_hasFDerivAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.cube_val`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.herm_inner`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.hermitian_posdef_open`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.hermitian_trace_one_chart_equiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.inverse_entry_contDiffAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.positive_chart_open`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.positive_hermitian_cube_derivative_equiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho_isHermitian`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.rho_trace`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.ricci`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.ricci_of_structure`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.scalarCurvature`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianHypersurfaceCalculus.structureRHS`
