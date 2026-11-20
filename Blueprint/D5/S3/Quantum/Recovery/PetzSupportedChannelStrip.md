# The supported-channel Petz strip identity

## Abstract

Two integrable boundary deficits of the actual supported channel overlap sum to its trace-log entropy loss.

Let Φ be a quantum channel between nonempty finite matrix spaces, and let ρ and σ be input density states with support of ρ contained in support of σ. Use the canonical supported relative modular data D of this channel and pair. The input coordinates (j,i) and output coordinates (l,k) range over the positive eigenvalues of the reference and source states on the corresponding spaces. Put a(j,i) = s(j)/r(i) and b(l,k) = q(l)/p(k), let V be the canonical matrix of the channel adjoint in weighted mixed eigenvector coordinates, and let ξ and η be the normalized input and output source vectors. For any real diagonal d on finite coordinates, its modular power P(d,z) has diagonal exp(log(d) z). The amplitude γ(z) is P(a,z) V P(b,−z) η. The finite overlap F(z) sums conj(ξ(x)) V(x,y) η(y) exp((log(a(x)) − log(b(y))) z) over input and output coordinates x and y. Write δ(r,s) = 2(1 − Re F(r + i s)).

**Theorem 1.1 (Physical channel amplitude).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any supported modular model M, complex z and input coordinate (j,i), γ(z)(j,i) is exp(log(a(j,i)) z) times √r(i) times the matrix element of Ψ(spectralX(P(b,−z) η)) between the reference eigenvector v(j) and source eigenvector u(i). Here Ψ is the actual channel adjoint and spectralX is the canonical output spectral reconstruction.

**Theorem 1.2 (Unrotated upper amplitude).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_half_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_half_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M and input coordinate (j,i), γ(1/2)(j,i) is √s(j) times the matrix element of Ψ(Q⁻¹ᐟ² T¹ᐟ²) between v(j) and u(i). Q and T are the actual output reference and source matrices. The inverse square root is the spectral inverse on the positive support and is zero on the kernel.

**Theorem 1.3 (Amplitude overlap).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_eq_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_eq_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all supported data D and z, F(z) = ⟨ξ, γ(z)⟩. Expanding the two diagonal powers gives the frequency difference in each summand.

**Theorem 1.4 (Normalization at zero).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_zero_re`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_zero_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any supported modular model M, Re F(0) = 1 because Vη = ξ and ξ has squared norm one.

**Theorem 1.5 (Adjoint at the normalized source).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.adjoint_mapsξ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.adjoint_mapsξ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M, Vᴴξ = η. The contraction V saturates its norm inequality on η because Vη = ξ and both vectors have norm one.

**Theorem 1.6 (Trace-log derivative).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.hasDerivAt_overlap_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.hasDerivAt_overlap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M, F has complex derivative at zero equal to the negative real trace-log relative entropy loss embedded in ℂ. The two logarithms in the finite frequency yield the input and output modular log expectations, and the adjoint identity sends the output term to the η expectation.

**Theorem 1.7 (Real part of the derivative).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deriv_overlap_zero_re`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deriv_overlap_zero_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M, Re F′(0) is the negative of the input trace-log relative entropy minus its output counterpart, with the negation applied to the entire loss.

**Theorem 1.8 (Upper comparison operator).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_eq_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_eq_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all supported data D, P(a,1/2) V P(b,−1/2) = cfc(√·, A) V cfc(1/√·, B), where A and B are the canonical diagonal relative modular matrices.

**Theorem 1.9 (Contraction at the upper edge).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M, the upper comparison operator C satisfies CᴴC ≤ 1 in the positive semidefinite order. Congruence by B⁻¹ᐟ² turns the canonical estimate VᴴAV ≤ B into this bound.

**Theorem 1.10 (Squared distance and lost norm).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deficit_eq_distance_add_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deficit_eq_distance_add_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M and real r and s, δ(r,s) equals the sum over input coordinates x of |ξ(x) − γ(r + i s)(x)|², plus one minus the sum over x of |γ(r + i s)(x)|².

**Theorem 1.11 (Lower boundary deficit).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.lower_deficit_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.lower_deficit_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M and real s, δ(0,s) ≥ 0. The imaginary powers are unitary on the supported coordinates and V is a contraction.

**Theorem 1.12 (Upper boundary deficit).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.upper_deficit_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.upper_deficit_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any M and real s, δ(1/2,s) ≥ 0. The imaginary powers act on the two sides of the upper comparison contraction.

**Theorem 1.13 (Integrable physical boundary deficits).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.integral_supported_channel_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.integral_supported_channel_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every Φ, ρ, σ and support containment as above, take D from supported_relative_modular_model Φ ρ σ. The function s ↦ lowerWeight(s) δ(0,s) is Lebesgue integrable on ℝ. The function s ↦ petzWeight(s) δ(1/2,s) is Lebesgue integrable on ℝ. The sum of the two whole-line integrals equals the trace-log relative entropy of ρ with respect to σ minus the trace-log relative entropy of Φ(ρ) with respect to Φ(σ). The lower weight is π/(cosh(2πs) − 1), with the totalized value at zero, and the upper weight is π/(cosh(2πs) + 1). Both integrands use the unsymmetrized overlap.

Yang’s Theorem II.1 gives the entropy-loss strip identity for faithful states. Section V.3 proposes the finite-dimensional extension under support containment. In the supported matrix model, normalization and the lower contraction verify the hypotheses of the finite exponential strip theorem at the singular boundary. The trace-log derivative identifies its right-hand side. Positive spectral coordinates and the canonical support reconstruction allow singular input and output density matrices.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.adjoint_mapsξ`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_coordinate`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.amplitude_half_coordinate`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deficit_eq_distance_add_defect`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.deriv_overlap_zero_re`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_contraction`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.halfComparison_eq_cfc`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.hasDerivAt_overlap_zero`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.integral_supported_channel_strip`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.lower_deficit_nonneg`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_eq_pair`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.overlap_zero_re`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.upper_deficit_nonneg`
- Dependency: [D5/S3/Analytic/PetzStripFiniteSeries](../../Analytic/PetzStripFiniteSeries.md)
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/ResolventDefectRigidity](../Divergence/ResolventDefectRigidity.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](PetzSpectralCoordinates.md)
