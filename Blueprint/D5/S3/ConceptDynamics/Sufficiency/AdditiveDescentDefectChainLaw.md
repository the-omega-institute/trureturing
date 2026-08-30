# Additive Descent Defect Chain Law

## Abstract

Additive descent defects obey the composition chain law.

**Theorem 1.1 (Additive defects compose by a chain law).**

$$\begin{aligned}\forall X, Y, Z, B_{C}, B_{D}, B_{E}: \operatorname{Type},\\{}[\operatorname{AddGroup}\left(B_{D}\right)], [\operatorname{AddGroup}\left(B_{E}\right)],\\F: X \to Y, G: Y \to Z,\\q_{C}: \operatorname{Concept}\left(X, B_{C}\right), q_{D}: \operatorname{Concept}\left(Y, B_{D}\right), q_{E}: \operatorname{Concept}\left(Z, B_{E}\right),\\\overline{F}: B_{C} \to B_{D}, \overline{G}: \operatorname{AddMonoidHom}\left(B_{D}, B_{E}\right),\\\varepsilon_{F} = (q_{D} \circ F - \overline{F} \circ q_{C}),\\\varepsilon_{G} = (q_{E} \circ G - \overline{G} \circ q_{D}),\\\varepsilon_{GF} = (q_{E} \circ G \circ F - \overline{G} \circ \overline{F} \circ q_{C}),\\\forall u, v\in B_{D}, \overline{G}(u+v) = \overline{G}(u)+\overline{G}(v),\\\varepsilon_{GF} = \varepsilon_{G} \circ F + \overline{G} \circ \varepsilon_{F}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw.additive_descent_defect_chain_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public definitions construct epsilon_F, epsilon_G, and epsilon_GF from the three readouts, two processes, and candidate macroscopic maps before the theorem relates those named objects.

The source declares the second macroscopic map as an ordinary function, but the equation requires it to preserve addition and subtraction. Lean records that repair as an AddMonoidHom, and the displayed additivity equation makes the added scope explicit.

After unfolding the named defects, the intermediate macroscopic readout cancels and preservation of subtraction leaves the composite defect.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/AdditiveDescentDefectChainLaw.additive_descent_defect_chain_law`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
