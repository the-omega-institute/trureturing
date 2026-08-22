# Reduced Record Access Defect

## Abstract

A reversible record coupling can preserve coherence globally while making it inaccessible to every reduced-state decoder.

**Theorem 1.1 (Reduced irreversibility is an access defect).**

$$\begin{gathered}\forall \rho, \sigma: \operatorname{QubitMatrix},\\{}(\forall i, \rho_{ii} = \sigma_{ii}) \land\\{}(\exists i, j, i \neq j \land \rho_{ij} \neq \sigma_{ij}) \Rightarrow\\{}\operatorname{Unitary}(U) \land\\{}\operatorname{evolve}(U, \operatorname{blank}(\rho)) = \operatorname{record}(\rho) \land\\{}\operatorname{evolve}(U, \operatorname{blank}(\sigma)) = \operatorname{record}(\sigma) \land\\{}\operatorname{traceEnvironment}(\operatorname{record}(\rho)) = \operatorname{traceEnvironment}(\operatorname{record}(\sigma)) \land\\{}\operatorname{record}(\rho) \neq \operatorname{record}(\sigma) \land\\{}(\neg\exists recover: \operatorname{QubitMatrix} \to \operatorname{JointQubitEnvironmentMatrix},\\{}(recover(\operatorname{traceEnvironment}(\operatorname{record}(\rho))) = \operatorname{record}(\rho) \land\\{}recover(\operatorname{traceEnvironment}(\operatorname{record}(\sigma))) = \operatorname{record}(\sigma))) \land\\{}\operatorname{evolve}(U^{*}, \operatorname{record}(\rho)) = \operatorname{blank}(\rho) \land\\{}\operatorname{evolve}(U^{*}, \operatorname{record}(\sigma)) = \operatorname{blank}(\sigma).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho and sigma be system matrices with the same populations and a different off-diagonal coherence. The environment begins in its blank address state, and a controlled-copy permutation writes the system address into the canonical environment-record state.

The permutation matrix is unitary and sends both blank-record inputs to their respective joint record states. Those joint states remain distinct, but tracing the environment makes the two reduced system states equal, so no function of that reduced state can reconstruct both phase-bearing joint records.

Applying the adjoint global coupling to either joint record restores its original blank-record input exactly. Thus the loss is caused by excluding the record degrees of freedom from the available control domain, not by irreversibility of the global evolution.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](ProjectedUnistochasticDynamics.md)
