# Saturated phase-memory equality

## Abstract

Equality constraints for the clipped guessing bound with one finite quantum memory.

A single CPTP channel receives the unknown quantum signal and sends an M-dimensional quantum system to the decoder. One POVM acts on that system alone. Visible encoding uses the classical label as input. An instrument with a retained classical outcome can also give the decoder a branch-dependent measurement. Those models have different feasible strategies.

**Theorem 1.1 (Equality fixes the compressed effects and one column of the pullbacks).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_local_effects_canonical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_local_effects_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the physical amplitudes as tᵢ = rᵢaᵢ with 0 < aᵢ ≤ 1 and Σᵢaᵢ² = M. The slopes satisfy rᵢ ≥ τ > 0, with rᵢ = τ wherever aᵢ < 1. At a saturated coordinate k, aₖ = 1. Dephase that column to one and assume the other column sums vanish and the vectors wⱼ = a · uⱼ are linearly independent. Positive amplitudes and a square orthogonal flat phase matrix give these independence and column-sum properties after dephasing.

Equality in the weighted rank-one estimate forces each score-preserving local effect to be a multiple of |wⱼ⟩⟨wⱼ|. These multiples sum to one. The aggregate effect has the same k-th column as the identity because the positive semidefinite slack has zero k-th diagonal entry. Independence gives the common multiple 1/N. The same zero-diagonal argument for the individual positive slacks gives Eⱼ(:,k) = Fⱼ(:,k).

**Theorem 1.2 (A saturated equality strategy needs N ≤ M²).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_channel_equality_card_le_memory_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_channel_equality_card_le_memory_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized inputs the spectral per-effect witness supplies score preservation and bounds the trace by that of the corresponding decoder effect. The pulled-back columns are independent at equality, so the decoder effects are complex-linearly independent in the M by M matrix space. The dimension bound concerns equality in the clipped guessing score.

**Theorem 1.3 (At N = M² the decoder effects form a tight projector frame).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.threshold_projector_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.threshold_projector_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Chefles, Richard Jozsa, Andreas Winter (2004). *On the existence of physical transformations between sets of quantum states*. DOI: [10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031). URL: <https://arxiv.org/abs/quant-ph/0307227>.

*Commentary.*

For normalized virtual vectors vⱼ = wⱼ/√M, the common dephased coordinate is 1/√M. Rank-one domination in the Stinespring pullback forces each decoder trace to be at least M/N. Since the traces sum to M, each trace equals M/N and each effect is (M/N)Qⱼ for a unit rank-one projector Qⱼ. The Qⱼ sum to (N/M)I.

The canonical columns intertwine the decoder action with the virtual vectors. At N = M² the Qⱼ span the full matrix space. The induced functional on matrices equals the normalized trace, so ⟨vⱼ,vₗ⟩ = Tr(QⱼQₗ). In particular, each entry is real and nonnegative. Chefles, Jozsa and Winter provide related pure-state transformation background. The equality argument here derives the projector frame from the guessing score.

**Theorem 1.4 (An asymmetric dominant Fourier ensemble cannot attain the clipped bound).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.fourier4_dominant_ne_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.fourier4_dominant_ne_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Chefles, Richard Jozsa, Andreas Winter (2004). *On the existence of physical transformations between sets of quantum states*. DOI: [10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031). URL: <https://arxiv.org/abs/quant-ph/0307227>.

*Commentary.*

For tᵢ > 0, Σᵢtᵢ² = 1 and t₀² ≥ 1/2, the clipped amplitudes are a₀ = 1 and aᵢ = tᵢ/r for i > 0, where r = √(t₁² + t₂² + t₃²). With uⱼᵢ = i to the power ji, the imaginary part of the normalized virtual Gram entry (0,1) is (a₁² − a₃²)/2. If t₁ ≠ t₃, this contradicts the projector Gram required for a qubit equality strategy.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.fourier4_dominant_ne_upper`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_channel_equality_card_le_memory_sq`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.saturated_local_effects_canonical`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.threshold_projector_gram`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordSpectralMemory](PhaseRecordSpectralMemory.md)
