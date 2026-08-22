# Experimental Quotient Universality

## Abstract

Intervention traces have the canonical empirical quotient universal property.

**Theorem 1.1 (The experimental quotient has the universal property).**

$$\begin{gathered}\forall A, X, B, Y: \operatorname{Type},\\{}F: A \to X \to X, O: X \to B, T: X \to Y,\\{}[\forall alpha: List(A), \exists! d_{alpha}: EmpiricalQuotient(experimentTrace(F, O)) \to List(B), experimentTrace(F, O)(alpha) = d_{alpha} \circ empiricalClass(experimentTrace(F, O))\\{}\land ((\forall x, y: X, (\forall alpha: List(A), experimentTrace(F, O)(alpha, x) = experimentTrace(F, O)(alpha, y)) \Rightarrow T(x) = T(y)) \Rightarrow \exists! d_{T}: EmpiricalQuotient(experimentTrace(F, O)) \to Y, T = d_{T} \circ empiricalClass(experimentTrace(F, O)))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/ExperimentalQuotientUniversality.experimental_quotient_universality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A protocol is a finite action list. Its trace is constructed from the intervention channel and public readout by recording the initial observation and every successive post-intervention observation.

The quotient and class map are the canonical objects imported from the empirical-identifiability family, instantiated with that trace readout rather than redefined for this theorem.

Every trace coordinate has a unique quotient factor. Independently, an arbitrary target has a unique quotient factor when it is constant on states with all the same traces.

Both clauses apply the existing unique-descent theorem directly. The converse constancy premise is local to the target clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/ExperimentalQuotientUniversality.experimental_quotient_universality`
- Dependency: [D5/S3/ConceptDynamics/EmpiricalIdentifiability](../EmpiricalIdentifiability.md)
