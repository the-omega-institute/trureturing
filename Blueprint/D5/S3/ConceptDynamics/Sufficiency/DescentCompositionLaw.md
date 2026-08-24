# Descent Composition Law

## Abstract

Exact descents through two successive readouts compose.

**Theorem 1.1 (Successive descents compose).**

$$\begin{aligned}\forall X, B, C: \operatorname{Type},\\F: X \to X, Fbar: B \to B, Ftilde: C \to C,\\q: X \to B, r: B \to C,\\q \circ F = Fbar \circ q \land r \circ Fbar = Ftilde \circ r \Rightarrow\\r \circ q \circ F = Ftilde \circ r \circ q.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw.descent_composition_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first equation says that the readout q carries the state update F to the intermediate update Fbar. The second says that r carries Fbar to Ftilde.

Substitution through the two commuting equations shows that the composite readout r after q carries F directly to Ftilde. No finiteness, topology, or inhabitedness assumption is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw.descent_composition_law`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency](FiniteWindowMinimalSufficiency.md)
