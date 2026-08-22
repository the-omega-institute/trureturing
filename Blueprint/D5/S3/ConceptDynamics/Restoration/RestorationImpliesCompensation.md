# Restoration Implies Compensation

## Abstract

Identity restoration preserves every value determined by identity.

**Theorem 1.1 (Identity restoration implies value compensation).**

$$\begin{gathered}X, B_{I}, B_{V}: \operatorname{Type},\\{}I: X \to B_{I}, V: X \to B_{V},\\{}U, R: X \to X,\\{}\operatorname{Refines}(V, I),\\{}\forall x, I(R(U(x))) = I(x),\\{}\Rightarrow \forall x, V(R(U(x))) = V(x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation.identity_restoration_implies_value_compensation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I record identity, let V record value or function, let U be the harm process, and let R be the repair process.

The refinement premise supplies a map from identity values to value values. Applying that map to the restored identity equality yields value compensation at every state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation.identity_restoration_implies_value_compensation`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
