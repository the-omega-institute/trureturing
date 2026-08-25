# Sensitive Leakage Monotonicity

## Abstract

Joining a fixed sensitive readout preserves concept refinement.

**Theorem 1.1 (Sensitive leakage is monotone under refinement).**

$$\forall X \in \operatorname{Type}, A \in \operatorname{Type}, B \in \operatorname{Type}, K \in \operatorname{Type}, C \in X \to A, D \in X \to B, S \in X \to K,\; \operatorname{Refines}\left(C, D\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(C, S\right), \operatorname{conceptJoin}\left(D, S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/SensitiveLeakageMonotonicity.sensitive_leakage_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current, refined, and sensitive readouts are independent public parameters. The premise says that the current readout factors through the refined one.

Both leakage objects are constructed with the canonical joint readout. The frozen augmentation law preserves the refinement while carrying the same sensitive coordinate on both sides.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/SensitiveLeakageMonotonicity.sensitive_leakage_monotone`
- Dependency: [D5/S3/ConceptDynamics/Dependency/BasicDependencyRules](../Dependency/BasicDependencyRules.md)
