# Phase-Damping Structure

## Abstract

Composition and fixed points delimit the stipulated qubit phase-damping channel.

**Theorem 1.1 (Phase-damping composition multiplies retention).**

$\forall c,d \in [0,1],\ \forall \rho \in \operatorname{QubitMatrix},\ \operatorname{phaseDamping}(c,\operatorname{phaseDamping}(d,\rho))=\operatorname{phaseDamping}(\operatorname{dampingProduct}(c,d),\rho)$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence.phase_damping_composition` (`✓ std3`). ∎

*Citation.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

DampingCoefficient is the inhabited real interval [0,1], with zero as an explicit witness. For an arbitrary complex two-by-two matrix, no positivity, trace-one, or Hermiticity premise is assumed. Composing two stipulated phase-damping maps multiplies their real coherence-retention coefficients. The theorem does not derive a channel from a system-environment Hamiltonian, identify the repository ledger with an environment, identify bookkeeping with decoherence, or make a record rule select a pointer basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N coherence law and fixed one-half populations are already formalized exactly by QubitWitnesses; the source atoms supply no fixed numeric c0 or N.

**Theorem 1.2 (Nontrivial phase damping fixes exactly diagonal matrices).**

$$\forall c \in [0,1],\ \forall \rho \in \operatorname{QubitMatrix},\ c\neq 1 \Rightarrow (\operatorname{phaseDamping}(c,\rho)=\rho \Leftrightarrow \forall i,j,\ i\neq j \Rightarrow \rho_{ij}=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal` (`✓ std3`). ∎

*Citation.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For a retention coefficient in [0,1] whose real value is explicitly not one, an arbitrary complex two-by-two matrix is fixed exactly when every off-diagonal entry vanishes. No positivity, normalization, Hermiticity, density-state, environment, or record-generation premise is hidden. This identifies the fixed points of the stipulated map only; it does not prove that address records physically select this basis or that Fourier records select another basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N law remains covered by the frozen QubitWitnesses theorem, with no fixed numeric c0 or N supplied by the atoms.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence.phase_damping_composition`
- Truth anchor: `D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal`
- Dependency: [D5/S3/Quantum/QubitWitnesses](QubitWitnesses.md)
