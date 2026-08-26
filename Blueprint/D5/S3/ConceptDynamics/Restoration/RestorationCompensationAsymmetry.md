# Restoration and Compensation Asymmetry

## Abstract

Identity restoration implies value compensation, but compensation need not restore identity.

**Theorem 1.1 (Restoration implies compensation and the converse fails).**

$$\begin{gathered}\forall X, IdentityValue, FunctionalValue: \operatorname{Type},\\{}I: X \to IdentityValue, V: X \to FunctionalValue,\\{}U, R: X \to X,\\{}\operatorname{Refines}(V, I),\\{}(\forall x, I(R(U(x))) = I(x)) \Rightarrow (\forall x, V(R(U(x))) = V(x)) \land\\{}\operatorname{let} I0: Bool \to Bool := id,\\{}\operatorname{let} V0: Bool \to Unit := (b \mapsto unit),\\{}\operatorname{let} U0: Bool \to Bool := \operatorname{BoolNot},\\{}\operatorname{let} R0: Bool \to Bool := id,\\{}\operatorname{Refines}(V0, I0) \land\\{}\forall b: Bool, V0(R0(U0(b))) = V0(b) \land\\{}\neg (\forall b: Bool, I0(R0(U0(b))) = I0(b)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/RestorationCompensationAsymmetry.identity_restoration_implies_compensation_with_converse_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward clause uses the canonical refinement relation to express that identity determines value.

The converse countermodel uses the same Boolean harm and repair in both halves: negation changes identity, while the constant unit-valued concept remains compensated.

All countermodel functions and their carriers are displayed explicitly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/RestorationCompensationAsymmetry.identity_restoration_implies_compensation_with_converse_countermodel`
- Dependency: [D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation](RestorationImpliesCompensation.md)
