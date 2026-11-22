# Optimized Walsh and Fourier phase-memory separation

## Abstract

The actual finite qubit guessing optima for dominant four-state Walsh and Fourier ensembles.

Four equiprobable phase signals have a common amplitude vector t with tᵢ > 0, Σᵢtᵢ² = 1 and t₀² ≥ 1/2. One CPTP encoder receives the unknown quantum signal. One four-outcome POVM acts only on its qubit output. Visible encoding knows the label, and a retained classical branch permits conditioned readout. The optimization here ranges over every CPTP encoder to a single qubit and every such POVM.

**Theorem 1.1 (The scalar clipping certificate bounds every qubit strategy).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.score_le_dominantBound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.score_le_dominantBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

The scalar M-distillation norm of Regula, Fang, Wang and Adesso gives the optimum of the diagonal-budget relaxation. For M = 2, put r = √(t₁² + t₂² + t₃²) and choose the feasible profile (1,(t₁/r)²,(t₂/r)²,(t₃/r)²). Its profile value is t₀ + r. Squaring and dividing by N = 4 gives the guessing bound for any unit-modulus phase entries. The coherence-distillation fidelity in Theorem 4 of Regula et al. uses division by M and optimizes a different task.

**Theorem 1.2 (Walsh attains the bound throughout the dominant family).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.walsh4_optimum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.walsh4_optimum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

The common Pauli encoder and its four effects realize (t₀ + r)²/4, which is also the upper bound for every qubit strategy.

**Theorem 1.3 (Fourier attains the bound exactly when t₁ = t₃).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.fourier4_optimum_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.fourier4_optimum_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric construction attains the bound at t₁ = t₃. If the two amplitudes differ, the real projector Gram required by saturated equality contradicts the virtual Gram. Compactness realizes the supremum, so exclusion of equality forces strict inequality for the actual optimum.

**Theorem 1.4 (Asymmetric Fourier phases give a strictly smaller optimized score than Walsh).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.phase_matrix_dependence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.phase_matrix_dependence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t = (4,1,2,2)/5, the squared amplitudes sum to one, t₀² = 16/25 and r = 3/5. Walsh attains ((4/5 + 3/5)²)/4 = 49/100. The same amplitudes give a strictly smaller Fourier optimum.

The virtual amplitudes before unit normalization are (1,1/3,2/3,2/3). With Fourier rows (1,1,1,1) and (1,i,−1,−i) for labels 0 and 1, the unit Gram entry is (1 + i/9 − 4/9 − 4i/9)/2 = 5/18 − i/6. The imaginary part witnesses the contradiction with a projector Gram.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.fourier4_optimum_eq_iff`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.phase_matrix_dependence`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.score_le_dominantBound`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.walsh4_optimum_eq`
- Dependency: [D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment](PhaseMemoryQubitAttainment.md)
- Dependency: [D5/S3/Quantum/PureState/QuantumMemoryBudget](QuantumMemoryBudget.md)
