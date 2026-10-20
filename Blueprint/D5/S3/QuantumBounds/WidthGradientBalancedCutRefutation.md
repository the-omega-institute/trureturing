# The balanced-cut gradient bound fails for eight qubits

## Abstract

Four singlets within the two halves of an eight-qubit chain have zero squared total spin and gradient second moment 240, exceeding the proposed balanced-cut bound 48.

The chain has N = 2m qubits. Fin m labels the half-sites by 0 through m − 1; the corresponding physical site labels start at one. Matrices act on complex amplitudes over the displayed computational bases. Matrix multiplication and matrix squares are operator multiplication, and a matrix numeral one is the identity. The Kronecker product orders the first half before the second.

**Definition 1.1 (The half and system spaces).**

$$\forall \left(m: \mathbb{N}\right), \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.Sys}\left(m\right) = \left(\left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right) \times \left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.Sys` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

Each half has computational basis Fin m → Fin 2 and Hilbert space ℂ^{Fin m → Fin 2}. The system basis is the ordered product of the two half bases, so its Hilbert space is the tensor product of the half spaces. The first factor contains physical sites 1 through m, and the second contains sites m + 1 through 2m.

**Definition 1.2 (An operator at one site).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(k: \operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)\right), \left(\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\left(\operatorname{Fin.val}\left(k\right) < m\right) \Rightarrow \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.siteOp}\left(m, k, A\right) = \operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(\operatorname{Fin.val}\left(k\right), A\right), 1\right)\right)\right) \land \left(\left(m \le \operatorname{Fin.val}\left(k\right)\right) \Rightarrow \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.siteOp}\left(m, k, A\right) = \operatorname{Matrix.kronecker}\left(1, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(\left(\operatorname{Fin.val}\left(k\right)\right) - \left(m\right), A\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.siteOp` (`✓ std3`).

*Citation.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

The operator localOp(j,A) applies A at half-site j and the identity at every other half-site. In the first branch the natural value k.val is read as an element of Fin m; in the second branch k.val − m is read that way. The branch inequalities ensure that these indices lie in Fin m. Thus the first m chain sites act on the first factor. The three Pauli matrices used in Appendix D are displayed below, in the order x, y, z; Complex.I is the imaginary unit and the nested brackets list matrix rows.

$$
\left(\operatorname{D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli}\left(0\right) = [[0, 1], [1, 0]]\right) \land \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli}\left(1\right) = [[0, -\operatorname{Complex.I}], [\operatorname{Complex.I}, 0]]\right) \land \left(\operatorname{D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli}\left(2\right) = [[1, 0], [0, -1]]\right)\right)
$$

**Definition 1.3 (Squared total spin).**

$$\forall \left(m: \mathbb{N}\right), \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.totalSpinSq}\left(m\right) = \sum_{l: \operatorname{Fin}\left(3\right)} \left(\left(\sum_{k: \operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)} \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.siteOp}\left(m, k, \operatorname{D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli}\left(l\right)\right)\right)\right)^{2}\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.totalSpinSq` (`✓ std3`).

*Citation.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

For each component ℓ, J_ℓ is the sum of its single-site Pauli operators. The operator J² is the sum of J_ℓ² over x, y, z. This is Pauli normalization, with no factor of one half in J_ℓ, as in the source.

**Definition 1.4 (The linear gradient weights).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(k: \operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)\right), \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.gradientWeight}\left(m, k\right) = \operatorname{Complex.ofReal}\left(\left(\left(\left(2\right) \cdot \left(\left(\left(\operatorname{Fin.val}\left(k\right)\right) + \left(1\right): \mathbb{R}\right)\right)\right) - \left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)\right) - \left(1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.gradientWeight` (`✓ std3`).

*Citation.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

For the one-based physical site q = k.val + 1, the weight is 2q − 2m − 1 = 2q − N − 1, as in Appendix D. The arithmetic inside Complex.ofReal is real, and its value is then embedded in ℂ. For m = 4 the weights are −7, −5, −3, −1, 1, 3, 5, 7.

**Definition 1.5 (Squared gradient spin).**

$$\forall \left(m: \mathbb{N}\right), \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.gradientSq}\left(m\right) = \sum_{l: \operatorname{Fin}\left(3\right)} \left(\left(\sum_{k: \operatorname{Fin}\left(\left(2\right) \cdot \left(m\right)\right)} \left(\operatorname{SMul.smul}\left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.gradientWeight}\left(m, k\right), \operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.siteOp}\left(m, k, \operatorname{D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli}\left(l\right)\right)\right)\right)\right)^{2}\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.gradientSq` (`✓ std3`).

*Citation.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

The gradient component B_ℓ weights each site Pauli by 2q − N − 1. The scalar action SMul.smul multiplies every entry of the site operator. The sum of the three component squares is B².

**Definition 1.6 (The proposed balanced-cut inequality).**

$$\left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.claim}\right) \Leftrightarrow \left(\forall \left(m: \mathbb{N}\right), \left(\left(2 \le m\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.Sys}\left(m\right), \operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.Sys}\left(m\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = 1\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.IsSeparable}\left(\rho\right)\right) \Rightarrow \left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.gradientSq}\left(m\right)\right)\right)\right) \le \left(\left(6\right) \cdot \left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)\right) + \left(\left(\frac{\left(\left(\frac{\left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)^{4}}{4}\right) + \left(\frac{\left(\left(\left(2\right) \cdot \left(\left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right) - \left(1\right)\right)\right) \cdot \left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)\right) \cdot \left(\left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right) + \left(1\right)\right)}{3}\right)\right) - \left(\left(6\right) \cdot \left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)\right)}{\left(2\right) \cdot \left(\left(2\right) \cdot \left(\left(m: \mathbb{R}\right)\right)\right)}\right) \cdot \left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.totalSpinSq}\left(m\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.claim` (`✓ std3`).

*Citation.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

Appendix D proposes this bound for all density matrices with entanglement only inside the two halves. Here N = 2m, m is any natural number at least two, and a density matrix is positive semidefinite with trace one. The predicate IsSeparable is the finite convex mixture of product density matrices across exactly this factorization, expanded below. The reference values are ⟨B²⟩₋ = 6N, ⟨J²⟩cl = 2N and ⟨B²⟩cl = N⁴/4 + 2(N − 1)N(N + 1)/3. The numerator uses this last second moment: the printed ⟨B⟩cl is read as ⟨B²⟩cl, consistently with the stated endpoints. At zero squared total spin this coefficient does not affect the bound. All arithmetic in the inequality is real.

$$
\forall \left(m: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.Sys}\left(m\right), \operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.Sys}\left(m\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.IsSeparable}\left(\rho\right)\right) \Leftrightarrow \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(p: \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right), \left(\exists \left(U: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right), \left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)\right)\right), \left(\exists \left(V: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right), \left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(t: \operatorname{Fin}\left(n\right)\right), \left(0 \le p\left(t\right)\right)\right) \land \left(\left(\sum_{t: \operatorname{Fin}\left(n\right)} \left(p\left(t\right)\right) = 1\right) \land \left(\left(\forall \left(t: \operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(U\left(t\right)\right)\right) \land \left(\left(\operatorname{Matrix.trace}\left(U\left(t\right)\right) = 1\right) \land \left(\left(\operatorname{Matrix.PosSemidef}\left(V\left(t\right)\right)\right) \land \left(\operatorname{Matrix.trace}\left(V\left(t\right)\right) = 1\right)\right)\right)\right)\right) \land \left(\rho = \sum_{t: \operatorname{Fin}\left(n\right)} \left(\operatorname{SMul.smul}\left(\operatorname{Complex.ofReal}\left(p\left(t\right)\right), \operatorname{Matrix.kronecker}\left(U\left(t\right), V\left(t\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)
$$

**Theorem 1.7 (A product of singlets violates the bound).**

$$\neg \operatorname{D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wolk-guhne-2016-balanced-cut-gradient-bound-refutation` (refuted) by `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wolk-guhne-2016-balanced-cut-gradient-bound-refutation","declaration_gid":"D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sabine Wölk; Otfried Gühne (2016). *Characterizing the width of entanglement*. DOI: [10.1088/1367-2630/aa5015](https://doi.org/10.1088/1367-2630/aa5015). URL: <https://arxiv.org/abs/1507.07226v2>.

*Commentary.*

Take m = 4 and N = 8. In each half let χ be the product of the normalized singlets (|01⟩ − |10⟩)/√2 on half-sites (1,4) and (2,3), using one-based labels. The normalized vector Φ = χ ⊗ χ defines the positive semidefinite density matrix ρ = |Φ⟩⟨Φ| of trace one. It is a product across the balanced cut, hence IsSeparable holds with one term of weight one. Each half is annihilated by every total-spin component, giving ⟨J²⟩ = 0. For each ℓ = x, y, z, the gradient component restricted to either half has mean zero and second moment ⟨B_ℓ²⟩ = 40: the paired weight differences have squares 6² and 2². The two half gradients have zero cross term in the product state, so the full component second moment is 80 and ⟨B²⟩ = 3 · (40 + 40) = 240. The proposed inequality of Wölk and Gühne instead gives ⟨B²⟩ ≤ 6N = 48 at ⟨J²⟩ = 0. Since 240 > 48, the universal claim is false. The singlets join sites inside each half; separability across the cut permits these nonadjacent pairs.

## References

- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.Sys`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.gradientSq`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.gradientWeight`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.siteOp`
- Truth anchor: `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.totalSpinSq`
- Dependency: [D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise](../Quantum/Entanglement/ElegantJointMeasurementSourceNoise.md)
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](../Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape](../Quantum/Magic/ThreeQubitStabilizerPolarEscape.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../Quantum/QuantumChannels/IptPptSquaredEquivalence.md)
