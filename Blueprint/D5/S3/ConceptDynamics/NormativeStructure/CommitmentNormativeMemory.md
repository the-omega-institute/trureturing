# Commitment Produces Normative Memory

## Abstract

Different committed permissions at one physical endpoint require normative memory.

**Theorem 1.1 (Committed permissions do not factor through physical state).**

$$\forall \Gamma, X, A: \operatorname{Type},\\{}e: \Gamma \to X, \pi_{P}: \Gamma \to \operatorname{Set}(A),\\{}\gamma, \gamma': \Gamma,\\{}(e(\gamma) = e(\gamma') \land \pi_{P}(\gamma) \neq \pi_{P}(\gamma')) \Rightarrow\\{}\neg (\exists q: X \to \operatorname{Set}(A), \pi_{P} = \operatorname{compose}(q, e)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeMemory.committed_permissions_do_not_factor_through_physical_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The history carrier, physical endpoint map, and committed future-permission readout are independent public source primitives on the canonical concept carrier.

Two public histories have the same physical endpoint and different committed permission sets. The conclusion directly denies every physical-state-only factorization of that readout.

The exact frozen family theorem for history-sensitive evaluation is imported and applied directly; no endpoint, permission readout, or factorization target is locally redefined.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeMemory.committed_permissions_do_not_factor_through_physical_state`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](HistorySensitiveOutcomeReductionObstruction.md)
