# Violation Enforceability Criterion

## Abstract

Exact violation enforcement is equivalent to audit-interface sufficiency, while a merged violation fiber forces an enforcement error.

**Theorem 1.1 (Exact enforcement requires a violation-sufficient audit interface).**

$$\forall Gamma \in \operatorname{Type}, BLog \in \operatorname{Type}, L \in \operatorname{Concept}\left(Gamma, BLog\right), V \in \operatorname{Concept}\left(Gamma, Bool\right),\; \operatorname{Nonempty}\left(Gamma\right) \Rightarrow \left(\left(\left(\exists e \in BLog \to Bool,\; V = e \circ L\right) \Leftrightarrow \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(V\right), L\right)\right) \land \left(\left(\forall gamma \in Gamma, gammaPrime \in Gamma,\; \left(L\left(gamma\right) = L\left(gammaPrime\right) \land V\left(gamma\right) \neq V\left(gammaPrime\right)\right) \Rightarrow \left(\forall e \in BLog \to Bool,\; e\left(L\left(gamma\right)\right) \neq V\left(gamma\right) \lor e\left(L\left(gammaPrime\right)\right) \neq V\left(gammaPrime\right)\right)\right) \land \left(\exists Vzero \in \operatorname{Concept}\left(Bool, Bool\right), Lzero \in \operatorname{Concept}\left(Bool, Unit\right),\; \left(\exists b \in Bool, bPrime \in Bool,\; Lzero\left(b\right) = Lzero\left(bPrime\right) \land Vzero\left(b\right) \neq Vzero\left(bPrime\right)\right) \land \left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(Vzero\right), Lzero\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Rights/ViolationEnforceabilityCriterion.violation_enforceability_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty event type, an exact Boolean enforcer exists precisely when the canonical effective violation target refines the audit log.

If two events have the same log value but different violation values, every enforcer restricted to that log value is wrong on at least one event.

The explicit Boolean countermodel has an identity violation target and a constant Unit-valued interface. It records a genuine violation distinction while proving that the interface is insufficient.

The nonempty-event premise is displayed because the canonical target image may otherwise be empty even though a raw Boolean executor exists.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Rights/ViolationEnforceabilityCriterion.violation_enforceability_criterion`
- Dependency: [D5/S3/ConceptDynamics/Communication/HeterogeneousFiberMisclassification](../Communication/HeterogeneousFiberMisclassification.md)
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](../Restoration/TargetRecoveryCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
