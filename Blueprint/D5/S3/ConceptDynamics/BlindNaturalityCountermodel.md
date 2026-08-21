# Blind Naturality Countermodel

## Abstract

A constant readout can commute with a process while losing target distinctions.

**Theorem 1.1 (A commuting constant readout need not preserve target distinctions).**

$$\exists C: Bool \to Unit, F: Bool \to Bool, K: Bool \to Bool,\ ((\exists Fbar: Unit \to Unit, C \operatorname{circ} F = Fbar \operatorname{circ} C) \land \neg \operatorname{Refines}(K, C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/BlindNaturalityCountermodel.blind_naturality_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source definitions distinguish a commuting macro square from faithfulness to a target. The countermodel constructs a constant readout from Boolean states to a one-point coordinate, an identity process, and a nonconstant Boolean target.

The first public clause exhibits the induced one-point process making the square commute. The second states that the target does not factor through the constant readout, proved by the two Boolean states.

Canonical Concept and Refines definitions are imported from the existing ConceptDynamics family. Searches found no exact countermodel theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/BlindNaturalityCountermodel.blind_naturality_counterexample`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](ConceptJoinUniversal.md)
