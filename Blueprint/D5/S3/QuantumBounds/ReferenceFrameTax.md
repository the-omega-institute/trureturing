# Reduced Reference-Frame Tax Identities

## Abstract

The flat and sine reference vectors have exact values for the reduced zero-boundary nearest-neighbour quadratic form, with an explicit one-level erratum and no claim of physical reduction or global optimality.

**Definition 1.1 (The nearest-neighbour quadratic form has zero boundary values).**

Lean statement: `D5/S3/QuantumBounds/ReferenceFrameTax.nearestNeighborQuadratic`

*Formalization.* `D5/S3/QuantumBounds/ReferenceFrameTax.nearestNeighborQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real vector indexed by Fin N, this definition sums the squares of the averages of the two neighbouring coordinates. A missing left or right neighbour contributes zero through the two dependent boundary tests. In the displayed presentation, each bold 1 is the indicator of its subscripted condition, so it is one exactly when the corresponding Lean branch supplies a coordinate and zero otherwise.

This is only the reduced finite real quadratic form. The module does not model or prove the reduction from an excitation-exchange unitary, a conservation-ladder reference, or entanglement fidelity to this expression; no certification of that physical reduction is claimed here.

**Theorem 1.2 (The flat reference has tax three over two N above one level).**

$$\forall N \in \mathbb{N},\ 2\leq N \Rightarrow 1-Q_{N}((\frac{1}{\sqrt{N}})_{m \in \operatorname{Fin}(N)})=\frac{3}{2N}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N with 2 <= N, the vector whose coordinates are all 1 / sqrt(N) has one minus its nearest-neighbour quadratic value equal to 3 / (2N). The lower bound on N is part of the theorem and cannot be dropped.

**Theorem 1.3 (The one-level flat reference has tax one).**

$$1-Q_{1}((\frac{1}{\sqrt{1}})_{m \in \operatorname{Fin}(1)})=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At N = 1 both neighbours are boundary zeros, so the quadratic value is zero and the tax is 1. It is not 3/2.

The source atom stated the flat formula without restricting N. This compiled boundary theorem records the resulting counterexample instead of silently narrowing the prose claim: the exception is a kernel-checked erratum. This is precisely what formalization is for: a boundary case that reads as harmless in prose does not survive the kernel.

**Theorem 1.4 (The box sine vector satisfies the coordinate recurrence).**

$$\forall N \in \mathbb{N},\ \forall m \in \operatorname{Fin}(N),\ \theta:=\frac{\pi}{N+1},\ c_{i}:=\sin((i+1)\theta),\ \frac{\mathbf{1}_{0<m} c_{m-1}+\mathbf{1}_{m+1<N} c_{m+1}}{2}=\operatorname{cos}(\theta)c_{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For theta = pi / (N+1), the coordinate vector sin((i+1) theta) is an eigenvector of zero-boundary nearest-neighbour averaging with eigenvalue cos(theta). The statement includes both dependent boundary tests and holds at every coordinate m in Fin N.

**Theorem 1.5 (The box sine vector has the eigenvalue quadratic value).**

$$\forall N \in \mathbb{N},\ \theta:=\frac{\pi}{N+1},\ Q_{N}((\sin((m+1)\theta))_{m \in \operatorname{Fin}(N)})=\operatorname{cos}(\theta)^{2} \sum_{m \in \operatorname{Fin}(N)} \sin((m+1)\theta)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_quadratic_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the squared coordinate recurrence gives the nearest-neighbour quadratic value of the unnormalized sine vector as cos(theta)^2 times the sum of sin((m+1) theta)^2. This is a witness equality, not an upper bound for arbitrary vectors.

**Theorem 1.6 (A unit sine reference attains the cosine-squared value).**

$$\forall N \in \mathbb{N},\ 1\leq N \Rightarrow \theta:=\frac{\pi}{N+1},\ \exists c:\operatorname{Fin}(N)\to \mathbb{R},\ (\sum_{i \in \operatorname{Fin}(N)} c_{i}^{2}=1) \land Q_{N}(c)=\operatorname{cos}(\theta)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.exists_unit_sine_reference_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= N, normalizing the box sine vector produces a real vector c with sum_i c_i^2 = 1 and nearest-neighbour quadratic value cos(pi/(N+1))^2. The theorem name says witness because it proves attainment only.

The missing half is the universal inequality asserting that every unit vector c satisfies Q(c) <= cos(pi/(N+1))^2. No packaged mathlib theorem was found for the required path-adjacency or tridiagonal operator norm. Consequently this module proves neither an IsGreatest statement nor the claimed optimal tax identity, and it does not prove the claimed two-dimensional degeneracy of the optimum.

**Theorem 1.7 (The flat and sine taxes coincide at two levels).**

$$1-Q_{2}((\frac{1}{\sqrt{2}})_{m \in \operatorname{Fin}(2)})=\sin(\frac{\pi}{2+1})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At N = 2, the compiled flat tax equals sin(pi/3)^2, hence 3/4. This checks coincidence with the sine-witness formula; by itself it does not establish global optimality.

**Theorem 1.8 (The flat and sine taxes coincide at three levels).**

$$1-Q_{3}((\frac{1}{\sqrt{3}})_{m \in \operatorname{Fin}(3)})=\sin(\frac{\pi}{3+1})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At N = 3, the compiled flat tax equals sin(pi/4)^2, hence 1/2. As in the two-level case, the theorem exercises the exact formulas without supplying the absent universal upper bound.

**Theorem 1.9 (The sine tax is strictly smaller than the flat tax at four levels).**

$$\sin(\frac{\pi}{4+1})^{2}<1-Q_{4}((\frac{1}{\sqrt{4}})_{m \in \operatorname{Fin}(4)})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTax.sine_tax_lt_flat_tax_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At N = 4, sin(pi/5)^2 is strictly smaller than the flat tax, which is 3/8. Numerically the sine tax is approximately 0.3454915, so the separation appears immediately after the two compiled coincidence cases.

These small cases keep both formulas exercised rather than merely stated. They show that the flat reference does not generally attain the sine-witness value, while making no unproved claim that the sine value is globally optimal.

Before formalization, the flat and sine formulas were compared numerically at N = 2, 3, 4, 6, and 10 to about 1e-16. Those checks remain external diagnostics, not certified statements in this document; the compiled N = 2, 3, and 4 declarations are the exact small-case results recorded here.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.exists_unit_sine_reference_witness`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax_one`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_three`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_two`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.nearestNeighborQuadratic`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_quadratic_witness`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.sine_tax_lt_flat_tax_four`
