# Old-Language Validity Conservativity

## Abstract

A projection that preserves admission and covers every admitted old state preserves and reflects validity of every old predicate.

**Theorem 1.1 (Old-language validity is conservative).**

$$\forall X \in \operatorname{Type}, XPrime \in \operatorname{Type}, Adm \in X \to Prop, AdmPrime \in XPrime \to Prop, p \in XPrime \to X, P \in X \to Prop,\; \left(\left(\forall xPrime \in XPrime,\; \operatorname{AdmPrime}\left(xPrime\right) \Rightarrow \operatorname{Adm}\left(\operatorname{p}\left(xPrime\right)\right)\right) \land \left(\forall x \in X,\; \operatorname{Adm}\left(x\right) \Rightarrow \left(\exists xPrime \in XPrime,\; \operatorname{AdmPrime}\left(xPrime\right) \land \operatorname{p}\left(xPrime\right) = x\right)\right)\right) \Rightarrow \left(\left(\forall x \in X,\; \operatorname{Adm}\left(x\right) \Rightarrow \operatorname{P}\left(x\right)\right) \Leftrightarrow \left(\forall xPrime \in XPrime,\; \operatorname{AdmPrime}\left(xPrime\right) \Rightarrow \operatorname{P}\left(\operatorname{p}\left(xPrime\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity.old_language_validity_conservative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first displayed premise expands admission preservation pointwise: an admitted extension state projects to an admitted old state. The second expands admitted-domain surjectivity: every admitted old state has an admitted extension preimage.

Preservation pulls old validity back along the projection. Reflection chooses an admitted preimage of each old state, so validity of the pullback returns validity of the original predicate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity.old_language_validity_conservative`
- Dependency: [D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation](../Transport/AdmissionValidityPreservation.md)
