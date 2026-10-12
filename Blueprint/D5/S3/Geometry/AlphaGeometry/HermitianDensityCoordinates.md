# HermitianDensityCoordinates

## Abstract

A real coordinate chart for Hermitian trace-one matrices.

**Definition 1.1 (G).**

$$\forall (n : \mathbb{N}), \forall (k : \operatorname{Fin}\left((n^{2}) - (1)\right)), \operatorname{G}\left(n, k\right) = \operatorname{fun} (r : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (s : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{let} row := \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(k\right), n\right); \operatorname{let} col := \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(k\right), n\right); \operatorname{if} (row = col) \operatorname{then} ((\operatorname{if} ((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = row)) \operatorname{then} (1) \operatorname{else} (0)) - (\operatorname{if} ((\operatorname{val}\left(r\right) = (n) - (1)) \land (\operatorname{val}\left(s\right) = (n) - (1))) \operatorname{then} (1) \operatorname{else} (0))) \operatorname{else} (\operatorname{if} (row < col) \operatorname{then} (\operatorname{if} (((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = col)) \lor ((\operatorname{val}\left(r\right) = col) \land (\operatorname{val}\left(s\right) = row))) \operatorname{then} (1) \operatorname{else} (0)) \operatorname{else} ((\operatorname{if} ((\operatorname{val}\left(r\right) = row) \land (\operatorname{val}\left(s\right) = col)) \operatorname{then} (\operatorname{Complex}.\operatorname{I}) \operatorname{else} (0)) - (\operatorname{if} ((\operatorname{val}\left(r\right) = col) \land (\operatorname{val}\left(s\right) = row)) \operatorname{then} (\operatorname{Complex}.\operatorname{I}) \operatorname{else} (0))))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural matrix-grid index omits the last diagonal position. Nat.div and Nat.mod are natural-number division and remainder. Diagonal directions subtract the final diagonal entry; the two ordered off-diagonal positions give the real and imaginary Hermitian directions.

**Definition 1.2 (rho).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{rho}\left(x\right) = (\frac{1}{n : \mathbb{R}}) \cdot (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) + \sum_{k : \operatorname{Fin}\left((n^{2}) - (1)\right)} ((x\left(k\right)) \cdot (\operatorname{G}\left(n, k\right)))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine chart has trace-one center and traceless Hermitian coordinate directions. Scalar multiplication is over the real numbers.

**Definition 1.3 (chartPoint).**

$$\forall (n : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{chartPoint}\left(A\right) = \operatorname{fun} (k : \operatorname{Fin}\left((n^{2}) - (1)\right)) \mapsto \operatorname{let} row := \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(k\right), n\right); \operatorname{let} col := \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(k\right), n\right); \operatorname{if} h : (row < n) \land (col < n) \operatorname{then} (\operatorname{let} entry := A\left(\langle row, h.1\rangle, \langle col, h.2\rangle\right); \operatorname{if} (row = col) \operatorname{then} ((entry.\operatorname{re}) - (\frac{1}{n : \mathbb{R}})) \operatorname{else} (\operatorname{if} (row < col) \operatorname{then} (entry.\operatorname{re}) \operatorname{else} (entry.\operatorname{im}))) \operatorname{else} 0$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.chartPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse chart reads the real upper entries, the imaginary lower entries, and the centered diagonal entries. The bound proof h supplies the two Fin indices. Nat.div and Nat.mod use natural-number division and remainder.

**Theorem 1.4 (rho_isHermitian).**

$$\forall (n : \mathbb{N}), \forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{rho}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every chart value is Hermitian.

**Theorem 1.5 (rho_trace).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{rho}\left(x\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive matrix dimension the chart value has trace one.

**Theorem 1.6 (chart_left_inverse).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R})), \operatorname{chartPoint}\left(\operatorname{rho}\left(x\right)\right) = x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.chart_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the coordinates of a chart value recovers every original coordinate.

**Theorem 1.7 (hermitian_trace_one_chart_equiv).**

$$\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(A\right) = 1) \Rightarrow (\operatorname{rho}\left(\operatorname{chartPoint}\left(A\right)\right) = A)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.hermitian_trace_one_chart_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reconstructing a Hermitian trace-one matrix from its chart coordinates recovers the matrix. The final diagonal coordinate follows from the trace equation.

**Theorem 1.8 (hermitian_posdef_open).**

$$\forall (n : \mathbb{N}), \operatorname{IsOpen}\left(\{A : \{A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) // \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)\} \mid \operatorname{Matrix}.\operatorname{PosDef}\left(\operatorname{val}\left(A\right)\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.hermitian_posdef_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definite matrices form an open set in the Hermitian subspace.

**Theorem 1.9 (positive_chart_open).**

$$\forall (n : \mathbb{N}), \operatorname{IsOpen}\left(\{x : (\operatorname{Fin}\left((n^{2}) - (1)\right)) \to (\mathbb{R}) \mid \operatorname{Matrix}.\operatorname{PosDef}\left(\operatorname{rho}\left(x\right)\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.positive_chart_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definiteness is an open condition in the density coordinates.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.G`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.chartPoint`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.chart_left_inverse`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.hermitian_posdef_open`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.hermitian_trace_one_chart_equiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.positive_chart_open`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho_isHermitian`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates.rho_trace`
