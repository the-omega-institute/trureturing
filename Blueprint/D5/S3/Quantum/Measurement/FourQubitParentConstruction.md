# FourQubitParentConstruction

## Abstract

FourQubitParentConstruction: exact analytic statements for four-qubit white-noise compatibility.

**Definition 1.1 (Compatible4).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \operatorname{Compatible4}\left(E\right) = \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPOVM}\left(E\left(i\right)\right)\right) \land \left(\exists J \in \left(\operatorname{Fin}\left(4\right) \to Bool\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsPOVM}\left(J\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; E\left(i, b\right) = \sum_{(e: \operatorname{Fin}\left(4\right) \to Bool), e\left(i\right) = b} J\left(e\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.Compatible4` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.13 (p. 12): “Let g ∈ ℕ, d ∈ ℕ, and kₓ ∈ ℕ for all x ∈ [g]. Let (Eᵢ∣ₓ)ᵢ∈[kₓ], x ∈ [g] be a collection of g d-dimensional POVMs. These measurements are compatible if there exists another d-dimensional POVM (Jᵢ₁,…,ᵢg)ᵢ₁∈[k₁],…,ᵢg∈[kg] such that” the marginal equality holds. Here g = 4, d = 2 and each outcome set is Bool. The sixteen functions Fin 4 → Bool index the joint outcomes; true denotes the positive sign.

**Definition 1.2 (noisy).**

$$\forall s \in \mathbb{R},\; \forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; \operatorname{noisy}\left(s, E, i, b\right) = (s) \cdot (E\left(i, b\right)) + (1 - s) \cdot (((\frac{1}{2}: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.noisy` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.15 (p. 13): “Let k ∈ ℕ and let (Eᵢ)ᵢ∈[k] be a POVM. Let s ∈ [0, 1] be a noise parameter. Then, we define the POVM (Eᵢ(s))ᵢ∈[k] with” Eᵢ(s) := sEᵢ + (1 − s)I/k “as the noisy version of (Eᵢ)ᵢ∈[k].” Here k = 2 and real scalars act on complex matrices.

**Definition 1.3 (endpoint).**

$$(endpoint: \mathbb{R}) = \frac{2}{\sqrt{13}}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sharp retained-signal parameter is 2/√13.

**Definition 1.4 (B).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(a\right) = ((a\left(0\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.X}\right)) + ((a\left(1\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.Y}\right)) + ((a\left(2\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.Z}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real coordinates multiply the three Pauli matrices.

**Theorem 1.5 (B_formula).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(a\right) = \begin{pmatrix}(a\left(2\right): \mathbb{C})&(a\left(0\right): \mathbb{C}) - \operatorname{Complex.I} \cdot (a\left(1\right): \mathbb{C})\\(a\left(0\right): \mathbb{C}) + \operatorname{Complex.I} \cdot (a\left(1\right): \mathbb{C})&-(a\left(2\right): \mathbb{C})\end{pmatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pauli expansion gives these four complex matrix entries.

**Theorem 1.6 (B_real_smul).**

$$\forall c \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left((c) \cdot (a)\right) = (c) \cdot (\operatorname{B}\left(a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_real_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bloch matrix is homogeneous for the real scalar action.

**Theorem 1.7 (B_neg).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(-a\right) = -\operatorname{B}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating the vector negates its Bloch matrix.

**Theorem 1.8 (B_sum).**

$$\forall U \in Type,\; \forall s \in \operatorname{Finset}\left(U\right),\; \forall a \in U \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(\sum_{i \in s} a\left(i\right)\right) = \sum_{i \in s} \operatorname{B}\left(a\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bloch expansion commutes with finite sums.

**Theorem 1.9 (norm_sq_coords).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert a \right\rVert^{2} = a\left(0\right)^{2} + a\left(1\right)^{2} + a\left(2\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.norm_sq_coords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared Euclidean norm is the sum of the three coordinate squares.

**Theorem 1.10 (trace_B_mul).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall b \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.trace}\left(\operatorname{B}\left(a\right) \cdot \operatorname{B}\left(b\right)\right) = (2 \cdot \operatorname{inner}\left(\mathbb{R}, a, b\right): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.trace_B_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace pairing of Bloch matrices is twice the real inner product.

**Definition 1.11 (scalarB).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{scalarB}\left(t, a\right) = ((t: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) + \operatorname{B}\left(a\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar identity is added to the traceless Bloch matrix.

**Theorem 1.12 (scalarB_posSemidef_iff).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{scalarB}\left(t, a\right)\right) \Leftrightarrow \left\lVert a \right\rVert \le t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant and diagonal entries give the necessary bound. At the boundary, the square identity expresses the matrix as a positive multiple of its conjugate-transpose square; adding a nonnegative scalar identity yields sufficiency.

**Theorem 1.13 (half_scalarB_posSemidef_iff).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.PosSemidef}\left(((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(t, a\right))\right) \Leftrightarrow \left\lVert a \right\rVert \le t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the positive scalar 1/2 preserves the positivity criterion.

**Theorem 1.14 (endpoint_mem_Icc).**

$$endpoint \in \operatorname{Set.Icc}\left(0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint_mem_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharp endpoint lies in the permitted retention interval.

**Theorem 1.15 (compatible_of_parent).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \forall J \in \left(\operatorname{Fin}\left(4\right) \to Bool\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsPOVM}\left(J\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; E\left(i, b\right) = \sum_{(e: \operatorname{Fin}\left(4\right) \to Bool), e\left(i\right) = b} J\left(e\right)\right) \Rightarrow \operatorname{Compatible4}\left(E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.compatible_of_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A POVM with these marginal sums establishes compatibility.

**Theorem 1.16 (all_povms_compatible).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPOVM}\left(E\left(i\right)\right)\right) \Rightarrow \operatorname{Compatible4}\left(\operatorname{noisy}\left(endpoint, E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.all_povms_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact convex sign decomposition follows from the four-vector inequality and the projection theorem. Antipodal effects give a joint parent for unbiased measurements. Each biased effect is obtained by a stochastic channel from a unit-vector effect and the two deterministic effects; applying these channels to the parent preserves every marginal.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_formula`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_neg`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_real_smul`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.Compatible4`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.all_povms_compatible`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.compatible_of_parent`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint_mem_Icc`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_posSemidef_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.noisy`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.norm_sq_coords`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_posSemidef_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.trace_B_mul`
- Dependency: [D5/S3/Geometry/FourVectorSignSumBound](../../Geometry/FourVectorSignSumBound.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
