# Exact Threshold for Byzantine Recovery

## Abstract

Universal deterministic Boolean recovery holds exactly above twice the fault bound.

**Theorem 1.1 (The strict honest-majority threshold is exact).**

$$\begin{aligned}\forall n, f \in \mathbb{N},\\(\exists recovery: (\operatorname{Fin}\left(n\right) \to Bool) \to Bool, \forall truth: Bool, reports: \operatorname{Fin}\left(n\right) \to Bool, \operatorname{byzantineCount}\left(reports, truth\right) \leq f \Rightarrow recovery(reports) = truth) \iff n > 2 \times f.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryExactThreshold.deterministic_recovery_exact_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reports form a Boolean vector indexed by Fin n. The canonical byzantineCount counts entries that disagree with the common truth, and the recovery rule receives only that report vector.

At or below twice the fault bound, the frozen impossibility theorem constructs one vector compatible with both truths. Above the bound, the canonical strict-majority rule returns the truth for every allowed report vector, proving the converse at the same threshold.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryExactThreshold.deterministic_recovery_exact_threshold`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryImpossibility](ByzantineRecoveryImpossibility.md)
