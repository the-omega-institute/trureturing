# Negativity does not imply positive reduction

## Abstract

A pure two-qutrit state has the attained negativity bound but fails positive reduction.

The partial transpose acts on the second factor, and the partial trace over that factor gives the first reduced state. Matrix.PosSemidef means positive semidefinite. The numeral one of matrix type is the identity matrix. The variable chi denotes χ; its casts to ℝ and ℂ are displayed separately. Matrix.kronecker denotes the Kronecker product ⊗ₖ, and SMul.smul denotes scalar multiplication.

**Definition 1.1 (Negativity from the trace norm).**

$$\forall \left(a: Type\right) \left(b: Type\right) [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(a \times b\right), \left(a \times b\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.negativity}\left(\rho\right): \mathbb{R}\right) = \frac{\left(\operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose}\left(\rho\right)\right)\right) - \left(1\right)}{2}\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.negativity` (`✓ std3`).

*Citation.* Jofre Abellanet-Vidal; Guillem Müller-Rigat; Albert Rico; Anna Sanpera (2026). *Bounding the entanglement of a state from its spectrum*. URL: <https://arxiv.org/abs/2604.02420v2>.

*Commentary.*

Definition 2, equation (7), defines N(ρ) = (‖ρ^Γ‖₁ − 1)/2. The trace norm is the real part of Tr √(A†A), and Γ transposes the second subsystem. This formula defines negativity on every complex matrix of the indicated size; the density-state conditions appear in the implication below.

**Definition 1.2 (The attained-value inclusion).**

$$\left(\left(\operatorname{D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.claim}: Prop\right)\right) \Leftrightarrow \left(\forall \left(a: Type\right) \left(b: Type\right) [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(a \times b\right), \left(a \times b\right), \mathbb{C}\right)\right), \left(\forall \left(chi: \mathbb{N}\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = 1\right) \Rightarrow \left(\left(1 \le chi\right) \Rightarrow \left(\left(chi \le \operatorname{Fintype.card}\left(a\right)\right) \Rightarrow \left(\left(chi \le \operatorname{Fintype.card}\left(b\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.negativity}\left(\rho\right) = \frac{\left(\left(chi: \mathbb{R}\right)\right) - \left(1\right)}{2}\right) \Rightarrow \left(\operatorname{Matrix.PosSemidef}\left(\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\rho\right), \left(1: \operatorname{Matrix}\left(b, b, \mathbb{C}\right)\right)\right)\right) - \left(\operatorname{SMul.smul}\left(\left(chi: \mathbb{C}\right)^{-1}, \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.claim` (`✓ std3`).

*Citation.* Jofre Abellanet-Vidal; Guillem Müller-Rigat; Albert Rico; Anna Sanpera (2026). *Bounding the entanglement of a state from its spectrum*. URL: <https://arxiv.org/abs/2604.02420v2>.

*Commentary.*

The hypothesis is the attained value N(ρ) = (χ − 1)/2, rather than the sublevel condition N(ρ) ≤ (χ − 1)/2 of Lemma 3. The attained-value hypothesis is stronger, so this universal implication is weaker than its sublevel form. Equation (35) gives RED_χ(X) = Tr(X)1 − X/χ, hence [1 ⊗ RED_χ](ρ) = ρ_A ⊗ 1 − ρ/χ, where ρ_A is the partial trace over the second subsystem. Theorem 7 states that failure of this positivity implies Schmidt number greater than χ. The question in §5.4 also has a non-FS reading, which is the implication displayed here. The FS inclusion, with its additional quantifier over global unitaries, is a separate question.

**Theorem 1.3 (The inclusion fails in dimension three).**

$$\neg \left(\operatorname{D5.S3.QuantumBounds.NegativityReductionInclusionRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/abellanet-vidal-muller-rigat-rico-sanpera-2026-negativity-reduction-inclusion` (refuted) by `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abellanet-vidal-muller-rigat-rico-sanpera-2026-negativity-reduction-inclusion","declaration_gid":"D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jofre Abellanet-Vidal; Guillem Müller-Rigat; Albert Rico; Anna Sanpera (2026). *Bounding the entanglement of a state from its spectrum*. URL: <https://arxiv.org/abs/2604.02420v2>.

*Commentary.*

Take ρ = |v⟩⟨v|/18 with v = 4|00⟩ + |11⟩ + |22⟩ and χ = 2. This is a positive semidefinite two-qutrit state of trace one. The trace norm of ρ^Γ is 2, so N(ρ) = 1/2 = (χ − 1)/2. Its reduced state is diag(16, 1, 1)/18. On the test vector |00⟩ + 4|11⟩ + 4|22⟩, the quadratic form of ρ_A ⊗ 1 − ρ/2 has value −4/3. Thus the reduction is not positive semidefinite. Because the negativity bound is attained, the same state also refutes the sublevel implication. This does not settle the FS inclusion.

## References

- Truth anchor: `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.negativity`
- Truth anchor: `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Quantum/Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Information/CoherentCopyCorrelationTax](../Quantum/Information/CoherentCopyCorrelationTax.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../Quantum/PureState/PureStateHandshake.md)
