# Equal-Superposition Coherence Decay

## Abstract

Strict phase damping drives equal-superposition coherence to zero.

**Theorem 1.1 (Equal-superposition coherence tends to zero).**

$$\lim_{N\to\infty} \operatorname{phaseDampingIterate}(c,N,\operatorname{equalSuperpositionDensity})_{01} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/CoherenceDecay.equal_superposition_coherence_tendsto_zero` (`✓ std3`). ∎

*Citation.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For a real phase-damping retention coefficient c in [0,1), the exact finite-step certificate identifies the equal-superposition off-diagonal entry with (1/2)c^N. Pinned Mathlib's geometric-power limit then sends that entry to zero. This closes only the source atom's exact coherence-decay clause; it does not derive the channel from a Hamiltonian or formalize the atom's center, pointer-basis, or redundancy claims.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/CoherenceDecay.equal_superposition_coherence_tendsto_zero`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../QubitWitnesses.md)
