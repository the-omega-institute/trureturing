# Admitted Validity Reflection

## Abstract

Surjectivity on admitted states reflects validity of pulled-back predicates.

**Theorem 1.1 (Admitted surjectivity reflects validity).**

$$\forall X \in \operatorname{Type}, Y \in \operatorname{Type}, AdmX \in X \to Prop, AdmY \in Y \to Prop, h \in X \to Y, P \in Y \to Prop,\; \left(\left(\forall y \in Y,\; AdmY\left(y\right) \Rightarrow \left(\exists x \in X,\; AdmX\left(x\right) \land h\left(x\right) = y\right)\right) \land \left(\forall x \in X,\; AdmX\left(x\right) \Rightarrow P\left(h\left(x\right)\right)\right)\right) \Rightarrow \left(\forall y \in Y,\; AdmY\left(y\right) \Rightarrow P\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection.validity_reflected_by_admitted_surjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admitted target state has an admitted source preimage. Pullback validity at that preimage transports along its displayed projection equality to validity of the target predicate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection.validity_reflected_by_admitted_surjection`
- Dependency: [D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity](OldLanguageValidityConservativity.md)
