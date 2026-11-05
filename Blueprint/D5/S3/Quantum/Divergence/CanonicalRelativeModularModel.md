# Actual relative modular model

## Abstract

Actual supported modular coordinates are shared by the original DPI and fixed Petz equality.

**Theorem 1.1 (The real quadratic form of a real diagonal matrix).**

$$\forall n \in \mathit{Type} u,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall d \in n \to \mathbb{R},\; \forall y \in n \to \mathbb{C},\; (\operatorname{dotProduct}\left(\operatorname{star}\left(y\right), \mathit{Matrix}.\mathit{mulVec}\left(\mathit{Matrix}.\mathit{diagonal}\left(\mathit{fun} i \mapsto (d\left(i\right):\mathbb{C})\right), y\right)\right)).\mathit{re} = \sum_{i} d\left(i\right) \cdot \left\lVert y\left(i\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.diagonal_quadratic_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, real weights and complex vector, the real part of the diagonal quadratic form is the weighted sum of squared norms. The weights need not be nonnegative, and the index type may be empty.

∀ {n : Type u} [Fintype n] [DecidableEq n] (d : n → ℝ) (y : n → ℂ), (star y ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ y)).re = ∑ i, d i * ‖y i‖ ^ 2.

**Definition 1.2 (Actual supported relative modular model).**

Lean statement: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model`

*Formalization.* `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same actual Phi, rho and sigma with input support containment, this constructor returns their relative modular coordinates, output support, exact same fixed Kraus family, both Schwarz inequalities, trace pairing, norm saturation and exact canonical entropy readouts. These facts are proved by the original DPI construction. The original DPI consumes this model and retains its original statement; CanonicalPetzEquality consumes it to derive recovery. This struct does not assume entropy equality or recovery.

**Definition 1.3 (Choose Kraus coordinates once from the channel).**

Lean statement: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation`

*Formalization.* `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This actual finite Kraus representation is chosen as a function only of Phi, before any density states. It carries both the Gram normalization and the full-matrix action. The construction was extracted once from the original DPI proof and is consumed by that DPI and the fixed-reference Petz theorem.

Faithful symmetric weights. Let a and b be arbitrary finite complex matrix carriers, Phi an actual completely positive trace-preserving channel, sigma a strictly positive density matrix, and tau=Phi(sigma) strictly positive. All matrix powers below are the real continuous functional calculus, so their eigenvalues are the corresponding scalar powers. The norm is the Frobenius, or Hilbert-Schmidt, norm, and star denotes conjugate transpose. Let T(X) denote the sandwiched channel map in the display. The following consequence uses the original model at rho=sigma and the original matrix Jensen results.

$\forall a \in \operatorname{FiniteTypes}\left(\right),\; \forall b \in \operatorname{FiniteTypes}\left(\right),\; \forall Phi \in \operatorname{QuantumChannel}\left(a, b\right),\; \forall sigma \in \operatorname{DensityState}\left(a\right),\; \left(\operatorname{PosDef}\left(\mathit{sigma}\right) \land \operatorname{PosDef}\left(\mathit{Phi}\left(\mathit{sigma}\right)\right)\right) \Rightarrow \left(\forall X \in \operatorname{Matrix}\left(a, a, \mathit{Complex}\right),\; \left\lVert \mathit{Phi}\left(\mathit{sigma}\right)^{-\frac{1}{4}} \cdot \mathit{Phi}\left(\mathit{sigma}^{\frac{1}{4}} \cdot X \cdot \mathit{sigma}^{\frac{1}{4}}\right) \cdot \mathit{Phi}\left(\mathit{sigma}\right)^{-\frac{1}{4}} \right\rVert \le \left\lVert X \right\rVert\right)$

Write Psi for the actual Kraus trace adjoint in supported_relative_modular_model Phi sigma sigma. In its spectral coordinates put A=diag(sigma_j/sigma_i), B=diag(tau_l/tau_k), and retain its actual matrix V. The model supplies V*V<=I, V*AV<=B, the coordinate action of V, and exact trace pairing with Phi. Operator convexity of minus square root gives V*sqrt(A)V<=sqrt(V*AV)<=sqrt(B). For the first inequality, the original isometry_jensen applies to W formed by stacking V and sqrt(I-V*V), and to diag(A,0); W*W=I. The original cfc_intertwining identifies the block square root. The second inequality is square-root monotonicity.

For every complex matrix Y, choose x_(l,k)=sqrt(tau_k)<w_l,Yw_k>. Faithfulness makes all spectral indices positive and the original spectral resolution of the identity reconstructs Y=spectralX(x). The original coordinateAction then gives (Vx)_(j,i)=sqrt(sigma_i)<v_j,Psi(Y)v_i>. The original full_spectral_parseval, cfc_mulVec_basis and basis_pair_cfc identify its sqrt(A) quadratic form with ||sigma^(1/4) Psi(Y) sigma^(1/4)||_HS^2. The sqrt(B) quadratic form is exactly ||tau^(1/4) Y tau^(1/4)||_HS^2. Here the weights are sqrt(sigma_j sigma_i), rather than a one-sided inverse-reference weight.

Define S(Y)=sigma^(1/4) Psi(tau^(-1/4) Y tau^(-1/4)) sigma^(1/4). The preceding inequality and cancellation of faithful quarter powers give ||S(Y)||_HS<=||Y||_HS. The actual tracePair and adjointStar fields give Tr(Y* T(X))=Tr(S(Y)* X). Taking Y=T(X), the original traceNorm_eq_max_re_tr_U and traceNorm_mul_le_hsSq bound ||T(X)||_HS^2 by ||S(T(X))||_HS ||X||_HS, hence by ||T(X)||_HS ||X||_HS. This proves the displayed bound, with the zero output handled without division. No self-adjointness, invertibility or nonzero condition is imposed on X; singular and zero inputs are included. No common eigenbasis for the reference, X or the channel coefficients is assumed. This consequence asserts neither recovery nor equality characterization.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation`
- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.diagonal_quadratic_form`
- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model`
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
