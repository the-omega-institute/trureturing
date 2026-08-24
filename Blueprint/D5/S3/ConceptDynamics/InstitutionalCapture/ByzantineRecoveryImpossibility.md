# Worst-Case Byzantine Recovery Impossibility

## Abstract

When no strict honest majority is guaranteed, report vectors cannot deterministically identify a Boolean truth under every allowed attack.

**Theorem 1.1 (No deterministic recovery at or below half).**

$$\begin{gathered}\forall n, f \in \mathbb{N}, n \leq 2 \times f\\{}\Rightarrow \neg\exists recovery: (\operatorname{Fin}\left(n\right) \to Bool) \to Bool,\\{}\forall truth: Bool, reports: \operatorname{Fin}\left(n\right) \to Bool,\\{}\operatorname{byzantineCount}\left(reports, truth\right) \leq f\Rightarrow recovery(reports) = truth.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryImpossibility.deterministic_recovery_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The report population is indexed by Fin n. The imported byzantineCount primitive counts reports that disagree with the common honest Boolean truth.

Under n at most two f, the proof constructs one report vector within the allowed f disagreements of both truth values. A deterministic rule would have to return false and true on that same vector.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryImpossibility.deterministic_recovery_impossible`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery](ByzantineMajorityRecovery.md)
