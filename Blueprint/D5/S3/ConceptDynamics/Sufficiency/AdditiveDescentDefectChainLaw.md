# Additive Descent Defect Chain Law

## Abstract

Additive descent defects obey the composition chain law.

**Theorem 1.1 (Additive defects compose by a chain law).**

$$\begin{aligned}\forall X, Y, Z, B_{C}, B_{D}, B_{E}: \operatorname{Type},\\{}[\operatorname{AddGroup}\left(B_{D}\right)], [\operatorname{AddGroup}\left(B_{E}\right)],\\F: X \to Y, G: Y \to Z,\\q_{C}: \operatorname{Concept}\left(X, B_{C}\right), q_{D}: \operatorname{Concept}\left(Y, B_{D}\right), q_{E}: \operatorname{Concept}\left(Z, B_{E}\right),\\\overline{F}: B_{C} \to B_{D}, \overline{G}: \operatorname{AddMonoidHom}\left(B_{D}, B_{E}\right),\\(q_{E} \circ G \circ F - \overline{G} \circ \overline{F} \circ q_{C}) = (q_{E} \circ G - \overline{G} \circ q_{D}) \circ F + \overline{G} \circ (q_{D} \circ F - \overline{F} \circ q_{C}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw.additive_descent_defect_chain_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three readouts and the two processes construct each defect directly as a difference of function composites. The first macroscopic map is arbitrary, while the second is additive because it transports the first defect.

Expanding the two terms on the right makes the intermediate macroscopic readout cancel. Additive preservation of subtraction then leaves exactly the defect of the composite process.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw.additive_descent_defect_chain_law`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw](DescentCompositionLaw.md)
