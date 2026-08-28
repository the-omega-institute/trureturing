# Experimental Quotient Characterization

## Abstract

Experimental targets are exactly functions on the empirical quotient.

**Theorem 1.1 (Experimental targets are quotient functions).**

$$\begin{aligned}\forall A: \operatorname{Type}, X: \operatorname{Type}, B: \operatorname{Type}, Y: \operatorname{Type},\\F: A \to \left(X \to X\right), O: X \to B, T: X \to Y,\\(\forall a: \operatorname{List}(A), \exists! d_{a}: \operatorname{EmpiricalQuotient}(\operatorname{experimentTrace}(F, O)) \to \operatorname{List}(B), \operatorname{experimentTrace}(F, O)(a) = d_{a} \circ \operatorname{empiricalClass}(\operatorname{experimentTrace}(F, O))) \land\\{}[(\exists! d_{T}: \operatorname{EmpiricalQuotient}(\operatorname{experimentTrace}(F, O)) \to Y, T = d_{T} \circ \operatorname{empiricalClass}(\operatorname{experimentTrace}(F, O)) \iff \forall x: X, y: X, (\forall a: \operatorname{List}(A), \operatorname{experimentTrace}(F, O)(a, x) = \operatorname{experimentTrace}(F, O)(a, y)) \Rightarrow T(x) = T(y)) \land\\((\exists x: X, y: X, (\forall a: \operatorname{List}(A), \operatorname{experimentTrace}(F, O)(a, x) = \operatorname{experimentTrace}(F, O)(a, y)) \land T(x) \neq T(y)) \Rightarrow \neg \exists d: \operatorname{EmpiricalQuotient}(\operatorname{experimentTrace}(F, O)) \to Y, T = d \circ \operatorname{empiricalClass}(\operatorname{experimentTrace}(F, O)))].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/ExperimentalQuotientCharacterization.experimental_quotient_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The protocol trace is the existing recursive trajectory constructed from the intervention channel and public readout. The quotient and class map are the canonical empirical objects for that trace.

Every trace coordinate has a unique quotient factor. For an arbitrary target, unique factorization is equivalent to constancy on states with every trace equal.

The final public clause is the converse obstruction: two states with all traces equal but different target values rule out every quotient factor for that target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/ExperimentalQuotientCharacterization.experimental_quotient_characterization`
- Dependency: [D5/S3/ConceptDynamics/Interventions/ExperimentalQuotientUniversality](../Interventions/ExperimentalQuotientUniversality.md)
