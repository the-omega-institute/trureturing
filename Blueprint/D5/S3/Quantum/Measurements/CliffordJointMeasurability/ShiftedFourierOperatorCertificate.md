# Shifted Fourier Operator Certificate

## Abstract

The sine-product weights admit a shifted Fourier reduction to a difference of positive weighted Laplacians.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Lemma 1.1 (sine weights path sum).**

$$\begin{aligned}\forall (K : \mathbb{N}),\\\operatorname{let} \theta : = \operatorname{Real} . \operatorname{pi} / ((K + 2 : \mathbb{N}) : \mathbb{R}) ; (\sum j \in \operatorname{Finset} . \operatorname{range} K , \operatorname{Real} . \operatorname{sin} (((j : \mathbb{R}) + 1) \cdot \theta) \cdot \operatorname{Real} . \operatorname{sin} (((j : \mathbb{R}) + 2) \cdot \theta)) = ((K + 2 : \mathbb{N}) : \mathbb{R}) / 2 \cdot \operatorname{Real} . \operatorname{cos} \theta\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.sine_weights_path_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This sine weights path sum identity is used in the ShiftedFourierOperatorCertificate construction.

**Definition 1.2 (theta).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\(\operatorname{theta} (L : = L) : \mathbb{R}) = (\operatorname{Real} . \operatorname{pi} / (2 \cdot (L : \mathbb{R})))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines theta.

**Lemma 1.3 (theta pos).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\(0 < L) \to\\0 < \operatorname{theta} L\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theta pos identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.4 (theta mul L).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\(0 < L) \to\\(L : \mathbb{R}) \cdot \operatorname{theta} L = \operatorname{Real} . \operatorname{pi} / 2\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta_mul_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theta mul L identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.5 (exponential sum orthogonality).**

$$\begin{aligned}\forall (M : \mathbb{N}),\\(0 < M) \to\\\forall (r : \operatorname{Fin} M),\\\forall (s : \operatorname{Fin} M),\\(\sum j \in \operatorname{Finset} . \operatorname{range} M , \operatorname{Complex} . \operatorname{exp} (((2 \cdot \operatorname{Real} . \operatorname{pi} \cdot ((r : \mathbb{R}) - (s : \mathbb{R})) / (M : \mathbb{R})) \cdot (j : \mathbb{R}) : \mathbb{R}) \cdot \operatorname{Complex} . I)) = \operatorname{if} r = s \operatorname{then} (M : \mathbb{C}) \operatorname{else} 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.exponential_sum_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This exponential sum orthogonality identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.6 (phase star).**

$$\begin{aligned}\forall (x : \mathbb{R}),\\\operatorname{star} ((\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) x) = (\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) (- x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This phase star identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.7 (phase mul).**

$$\begin{aligned}\forall (x : \mathbb{R}),\\\forall (y : \mathbb{R}),\\(\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) x \cdot (\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) y = (\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) (x + y)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This phase mul identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.8 (phase cos).**

$$\begin{aligned}\forall (x : \mathbb{R}),\\(\operatorname{Real} . \operatorname{cos} x : \mathbb{C}) = ((\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) x + (\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) (- x)) / 2\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_cos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This phase cos identity is used in the ShiftedFourierOperatorCertificate construction.

**Definition 1.9 (pathWeight).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\forall (j : \mathbb{R}),\\(\operatorname{pathWeight} (L : = L) (j : = j) : \mathbb{R}) = ((\operatorname{Real} . \operatorname{cos} (\operatorname{theta} L) - \operatorname{Real} . \operatorname{cos} ((2 \cdot j + 1) \cdot \operatorname{theta} L)) / 2)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pathWeight.

**Definition 1.10 (pathDualWeight).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\\forall (k : \operatorname{Fin} (2 \cdot n)),\\(\operatorname{pathDualWeight} (n : = n) (k : = k) : \mathbb{R}) = (\operatorname{pathWeight} (n + 1) ((k : \mathbb{R}) + 1))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathDualWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pathDualWeight.

**Definition 1.11 (padCompression).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\(\operatorname{padCompression} (d : = d) : \operatorname{Matrix} ((\operatorname{Fin} d \times \operatorname{Fin} 2) \times \operatorname{Fin} 2) (\operatorname{Fin} d) \mathbb{C}) = ((\operatorname{qubitV} (\iota : = \operatorname{Fin} d \times \operatorname{Fin} 2) : \operatorname{Matrix} ((\operatorname{Fin} d \times \operatorname{Fin} 2) \times \operatorname{Fin} 2) (\operatorname{Fin} d \times \operatorname{Fin} 2) \mathbb{C}) \cdot ((\operatorname{qubitV} (\iota : = \operatorname{Fin} d)) : \operatorname{Matrix} (\operatorname{Fin} d \times \operatorname{Fin} 2) (\operatorname{Fin} d) \mathbb{C}))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines padCompression.

**Lemma 1.12 (padCompression isometry).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\(\operatorname{padCompression} d) . \operatorname{conjTranspose} \cdot \operatorname{padCompression} d = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This padCompression isometry identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.13 (padCompression compress).**

$$\begin{aligned}\forall (d : \mathbb{N}),\\\forall (B : (\operatorname{Matrix} (\operatorname{Fin} d \times \operatorname{Fin} 2) (\operatorname{Fin} d \times \operatorname{Fin} 2) \mathbb{C})),\\(\operatorname{padCompression} d) . \operatorname{conjTranspose} \cdot (B (\operatorname{Matrix}.\operatorname{kronecker}) (1 : \operatorname{Matrix} (\operatorname{Fin} 2) (\operatorname{Fin} 2) \mathbb{C})) \cdot \operatorname{padCompression} d = ((\operatorname{qubitV} (\iota : = \operatorname{Fin} d))) . \operatorname{conjTranspose} \cdot B \cdot (\operatorname{qubitV} (\iota : = \operatorname{Fin} d))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression_compress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This padCompression compress identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.14 (pathWeight sine).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\forall (j : \mathbb{R}),\\\operatorname{pathWeight} L j = \operatorname{Real} . \operatorname{sin} (j \cdot \operatorname{theta} L) \cdot \operatorname{Real} . \operatorname{sin} ((j + 1) \cdot \operatorname{theta} L)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathWeight_sine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This pathWeight sine identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.15 (path dual operator certificate).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\\forall (d : \mathbb{N}),\\(1 \leq n) \to\\\forall (A : \operatorname{Fin} (2 \cdot n) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})),\\(\operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{pathGraph} (2 \cdot n)) A) \to\\\forall (a : \operatorname{Fin} (2 \cdot n) \to \operatorname{Bool}),\\(((\operatorname{Real} . \operatorname{cos} (\operatorname{theta} (n + 1)) / \operatorname{Real} . \operatorname{sin} (\operatorname{theta} (n + 1)) : \mathbb{C})) \cdot (1 : (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C})) - \operatorname{weightedHamiltonian} A (\operatorname{pathDualWeight} n) a) . \operatorname{PosSemidef}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.path_dual_operator_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine-product weights admit a shifted Fourier reduction to a difference of positive weighted Laplacians. Its positive trace is cot(theta (n+1)). The Majorana quadratic bound and the ancilla compression give this operator inequality for every path realization and every Boolean outcome.

**Lemma 1.16 (visibility as L).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\\operatorname{visibility} n = 1 / (((n + 1 : \mathbb{N}) : \mathbb{R}) \cdot \operatorname{Real} . \operatorname{sin} (\operatorname{theta} (n + 1)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_as_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This visibility as L identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.17 (visibility Icc).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\(1 \leq n) \to\\\operatorname{visibility} n \in \operatorname{Set} . \operatorname{Icc} (0 : \mathbb{R}) 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This visibility Icc identity is used in the ShiftedFourierOperatorCertificate construction.

**Lemma 1.18 (visibility upper of weighted).**

$$\begin{aligned}\forall (n : \mathbb{N}),\\(1 \leq n) \to\\\forall (t : \mathbb{R}),\\(t \cdot (((n + 1 : \mathbb{N}) : \mathbb{R}) \cdot \operatorname{Real} . \operatorname{cos} (\operatorname{theta} (n + 1))) \leq \operatorname{Real} . \operatorname{cos} (\operatorname{theta} (n + 1)) / \operatorname{Real} . \operatorname{sin} (\operatorname{theta} (n + 1))) \to\\t \leq \operatorname{visibility} n\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_upper_of_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This visibility upper of weighted identity is used in the ShiftedFourierOperatorCertificate construction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.exponential_sum_orthogonality`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression_compress`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.padCompression_isometry`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathDualWeight`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathWeight`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.pathWeight_sine`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.path_dual_operator_certificate`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_cos`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_mul`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.phase_star`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.sine_weights_path_sum`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta_mul_L`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.theta_pos`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_Icc`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_as_L`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.visibility_upper_of_weighted`
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../../Dynamics/PolygonalFourierCouplings.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations](CliffordPathRealizations.md)
