# Identity Restoration and Value Compensation

## Abstract

Identity restoration preserves identity-determined value, while equal-value compensation need not restore identity.

**Theorem 1.1 (Restoration implies compensation but not conversely).**

$$\begin{gathered}(\forall X, B_{I}, B_{V}: \operatorname{Type},\\{}I: X \to B_{I}, V: X \to B_{V},\\{}U, R: X \to X,\\{}\operatorname{Refines}(V, I) \land (\forall x: X, I(R(U(x))) = I(x)) \Rightarrow (\forall x: X, V(R(U(x))) = V(x))) \land\\{}(\operatorname{let} I_{c}: Bool \to Bool := (b \mapsto b), V_{c}: Bool \to Unit := (b \mapsto *), U_{c}: Bool \to Bool := (b \mapsto \neg b), R_{c}: Bool \to Bool := (b \mapsto b), \operatorname{in} (\operatorname{Refines}(V_{c}, I_{c}) \land (\forall b: Bool, V_{c}(R_{c}(U_{c}(b))) = V_{c}(b)) \land \neg (\forall b: Bool, I_{c}(R_{c}(U_{c}(b))) = I_{c}(b)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/IdentityRestorationValueCompensation.identity_restoration_implies_value_compensation_and_converse_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward clause applies the frozen restoration theorem directly: a factor from identity values to functional values transports the restored-identity equality to value compensation.

The converse clause uses one shared two-state construction. Identity is the Bool identity readout, value is constant Unit, harm swaps the states, and repair is the identity process. The common value is preserved although the state identity is not restored.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/IdentityRestorationValueCompensation.identity_restoration_implies_value_compensation_and_converse_countermodel`
- Dependency: [D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation](RestorationImpliesCompensation.md)
