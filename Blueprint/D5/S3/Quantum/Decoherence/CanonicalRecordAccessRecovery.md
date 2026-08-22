# Canonical Record Access Recovery

## Abstract

A reversible coupling preserves phase information in the canonical environment record even when that information is unavailable from the reduced state.

**Theorem 1.1 (Reduced irreversibility is a canonical record access defect).**

$$\begin{gathered}\forall \rho, \sigma: \operatorname{QubitMatrix},\\{}(\forall i, \rho_{ii} = \sigma_{ii}) \land\\{}(\exists i, j, i \neq j \land \rho_{ij} \neq \sigma_{ij}) \Rightarrow\\{}\operatorname{Unitary}\left(U\right) \land\\{}\operatorname{evolve}\left(U, \operatorname{blank}\left(\rho\right)\right) = \operatorname{canonicalRecord}\left(\rho\right) \land\\{}\operatorname{evolve}\left(U, \operatorname{blank}\left(\sigma\right)\right) = \operatorname{canonicalRecord}\left(\sigma\right) \land\\{}\operatorname{traceEnvironment}\left(\operatorname{canonicalRecord}\left(\rho\right)\right) = \operatorname{traceEnvironment}\left(\operatorname{canonicalRecord}\left(\sigma\right)\right) \land\\{}\operatorname{canonicalRecord}\left(\rho\right) \neq \operatorname{canonicalRecord}\left(\sigma\right) \land\\{}(\neg\exists recover: \operatorname{QubitMatrix} \to \operatorname{JointQubitEnvironmentMatrix},\\{}(recover(\operatorname{traceEnvironment}\left(\operatorname{canonicalRecord}\left(\rho\right)\right)) = \operatorname{canonicalRecord}\left(\rho\right) \land\\{}recover(\operatorname{traceEnvironment}\left(\operatorname{canonicalRecord}\left(\sigma\right)\right)) = \operatorname{canonicalRecord}\left(\sigma\right))) \land\\{}\operatorname{evolve}\left(U^{*}, \operatorname{canonicalRecord}\left(\rho\right)\right) = \operatorname{blank}\left(\rho\right) \land\\{}\operatorname{evolve}\left(U^{*}, \operatorname{canonicalRecord}\left(\sigma\right)\right) = \operatorname{blank}\left(\sigma\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.reduced_irreversibility_is_canonical_record_access_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho and sigma be system matrices with the same populations and a different off-diagonal coherence. The controlled-copy permutation writes each input into the canonical copied-address environment record.

The permutation matrix is unitary and produces both joint record states. Those states remain distinct, but tracing the environment makes their reduced system states equal, so no one function of the reduced state can reconstruct both joint records.

Applying the adjoint global coupling to either canonical joint record restores its original blank-record input exactly. Global reversible generation therefore does not imply local engineering recovery when the phase-bearing record is outside the available control domain.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.reduced_irreversibility_is_canonical_record_access_defect`
- Dependency: [D5/S3/Observer/MeasurementMarginal](../../Observer/MeasurementMarginal.md)
- Dependency: [D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect](ReducedRecordAccessDefect.md)
