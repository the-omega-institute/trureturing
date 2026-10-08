# The Appendix A.1 feasible tuple

## Abstract

The six real symmetric matrices of Appendix A.1 are positive semidefinite over the complex numbers and satisfy all four affine constraints throughout the closed interval.

**Definition 1.1 (X₁).**

$$(X_{1}: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = \begin{pmatrix}1 & 0\\0 & -2\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first real matrix is diagonal with entries 1 and -2.

**Definition 1.2 (X₂).**

$$(X_{2}: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = \begin{pmatrix}-2 & 0\\0 & 1\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second real matrix is diagonal with entries -2 and 1.

**Definition 1.3 (X₃).**

$$\forall (\theta: \mathbb{R}), (X_{3}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = \begin{pmatrix}\operatorname{cos}(\theta) & \operatorname{sin}(\theta)\\\operatorname{sin}(\theta) & -\operatorname{cos}(\theta)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real angle, the third matrix has cosine on the first diagonal entry, negative cosine on the second, and sine off the diagonal.

**Definition 1.4 (The normalization constant).**

$$(\gamma: \mathbb{R}) = \frac{4}{1+\sqrt{3}}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real scalar gamma normalizes the sum of the six matrices.

**Definition 1.5 (The radical).**

$$\forall (\theta: \mathbb{R}), (\beta(\theta): \mathbb{R}) = \sqrt{3} \sqrt{(6-4 \sqrt{3}) \operatorname{sin}(\theta)+6 \operatorname{cos}(\theta)-4 \sqrt{3}+13}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The principal real square roots define beta for every real angle.

**Definition 1.6 (C₁).**

$$(C_{1}: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = (\frac{1}{\sqrt{3}}-\frac{1}{2}) \cdot \begin{pmatrix}1 & 1\\1 & 1\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first matrix is a positive scalar multiple of the all-ones matrix.

**Definition 1.7 (C₂).**

$$\forall (\theta: \mathbb{R}), (C_{2}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = \frac{1}{12} \cdot \begin{pmatrix}3 \operatorname{cos}(\theta)+8 \sqrt{3}-9-\beta(\theta) & 3 \operatorname{sin}(\theta)-2 \sqrt{3}+3\\3 \operatorname{sin}(\theta)-2 \sqrt{3}+3 & -3 \operatorname{cos}(\theta)+8 \sqrt{3}-3-\beta(\theta)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second real symmetric matrix depends on the sine, cosine and radical of the angle.

**Definition 1.8 (C₃).**

$$\forall (\theta: \mathbb{R}), (C_{3}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = -C_{1}-C_{2}(\theta)+\frac{1}{2} \cdot X_{3}(\theta)+\frac{\gamma}{2} \cdot I_{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third matrix is an affine combination of the first two matrices, X₃ and the normalization constant.

**Definition 1.9 (C₄).**

$$\forall (\theta: \mathbb{R}), (C_{4}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = -C_{1}+\frac{1}{3} \cdot X_{1}+\frac{1}{3} \cdot X_{2}+\frac{\gamma}{3} \cdot I_{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fourth matrix is an affine combination of C₁, X₁, X₂ and the normalization constant. Its value is independent of the real angle.

**Definition 1.10 (C₅).**

$$\forall (\theta: \mathbb{R}), (C_{5}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = -C_{2}(\theta)-\frac{1}{3} \cdot X_{1}+\frac{\gamma}{3} \cdot I_{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fifth matrix is an affine combination of C₂, X₁ and gamma.

**Definition 1.11 (C₆).**

$$\forall (\theta: \mathbb{R}), (C_{6}(\theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = C_{1}+C_{2}(\theta)-\frac{1}{3} \cdot X_{2}-\frac{1}{2} \cdot X_{3}(\theta)-\frac{\gamma}{6} \cdot I_{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sixth matrix is an affine combination of C₁, C₂, X₂, X₃ and gamma.

**Definition 1.12 (The indexed family).**

$$\forall (i: \operatorname{Fin}(6)), \forall (\theta: \mathbb{R}), (\operatorname{C}(i, \theta): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R})) = (C_{1}, C_{2}(\theta), C_{3}(\theta), C_{4}(\theta), C_{5}(\theta), C_{6}(\theta))_{i}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indices 0 through 5 correspond in order to C₁ through C₆. Every value is a real 2 by 2 matrix.

**Definition 1.13 (Appendix A.1 feasibility).**

$$(claim: Prop) := \forall (\theta: \mathbb{R}), \theta \in \operatorname{Icc}(0, \frac{\pi}{2}) \Rightarrow (\forall (i: \operatorname{Fin}(6)), (\operatorname{C}(i, \theta).\operatorname{map}(ofReal): \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C})).PosSemidef) \land \operatorname{C}(0, \theta)-2 \cdot \operatorname{C}(1, \theta)+\operatorname{C}(2, \theta)+\operatorname{C}(3, \theta)-2 \cdot \operatorname{C}(4, \theta)+\operatorname{C}(5, \theta) = X_{1} \land \operatorname{C}(0, \theta)+\operatorname{C}(1, \theta)-2 \cdot \operatorname{C}(2, \theta)+\operatorname{C}(3, \theta)+\operatorname{C}(4, \theta)-2 \cdot \operatorname{C}(5, \theta) = X_{2} \land \operatorname{C}(0, \theta)+\operatorname{C}(1, \theta)+\operatorname{C}(2, \theta)-\operatorname{C}(3, \theta)-\operatorname{C}(4, \theta)-\operatorname{C}(5, \theta) = X_{3}(\theta) \land \sum_{i: \operatorname{Fin}(6)} \operatorname{C}(i, \theta) = \gamma \cdot I_{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Feasibility for every angle in [0, pi/2] consists of positive semidefiniteness of the six complex images and the four displayed affine equations. The map uses the standard real-to-complex inclusion; the identity is the real 2 by 2 identity matrix. Positive semidefiniteness requires nonnegative determinants.

**Theorem 1.14 (Feasibility throughout the closed interval).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.result` (`✓ std3`). ∎

*Resolves.* `Problems/bluhm-2025-appendix-a1-feasibility` (proved) by `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bluhm-2025-appendix-a1-feasibility","declaration_gid":"D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The six matrices satisfy the four affine identities. A real symmetric 2 by 2 matrix with positive trace and nonnegative determinant has a nonnegative complex quadratic form. The first and fourth matrices have positive trace and zero determinant, as do the third and fifth. For the second matrix, squaring and factoring the radical comparison gives a product of 1 minus sine with a strictly positive factor. Its determinant is therefore nonnegative and its trace is positive. The sixth matrix has the same trace and determinant as the second.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C1`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C2`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C3`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C4`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C5`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.C6`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X1`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X2`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.X3`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.beta`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.gamma`
- Truth anchor: `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.result`
- Dependency: [D5/S3/Constants/Radicals/SqrtThreeThreshold](../../Constants/Radicals/SqrtThreeThreshold.md)
