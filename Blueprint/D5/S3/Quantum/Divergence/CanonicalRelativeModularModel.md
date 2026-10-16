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

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation`
- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.diagonal_quadratic_form`
- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model`
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
