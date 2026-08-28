# Controlled Completion Descent

## Abstract

Canonical controlled updates and readouts are the unique maps descending to completion.

**Theorem 1.1 (Controlled updates and the joint readout descend canonically).**

$$\forall U \in \operatorname{Type}, Y \in \operatorname{Type}, O \in \operatorname{Type}, F \in U \to \left(Y \to Y\right), q \in Y \to O,\; (\forall u \in U, G \in \operatorname{ControlledCompletion}\left(F, q\right) \to \operatorname{ControlledCompletion}\left(F, q\right),\; (\operatorname{completionProjection}\left(F, q\right) \circ F\left(u\right) = G \circ \operatorname{completionProjection}\left(F, q\right)) \iff G = \operatorname{completionUpdate}\left(F, q, u\right)) \land (\forall r \in \operatorname{ControlledCompletion}\left(F, q\right) \to O,\; (q = r \circ \operatorname{completionProjection}\left(F, q\right)) \iff r = \operatorname{completionReadout}\left(F, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent.controlled_completion_update_and_readout_descend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the existing quotient by equality of all readouts after finite input words. Its projection, input-indexed updates, and current readout are the canonical controlled-completion objects.

For every input, an endomap commutes with the quotient projection exactly when it is the canonical completion update. A readout from the quotient factors the original readout exactly when it is the canonical completion readout.

The update half applies the frozen unique controlled-descent theorem. The readout half uses surjectivity of the quotient projection to prove uniqueness on every completed state.

Repository search found the update-only unique descent theorem but no statement carrying the joint-readout descent clause as well.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent.controlled_completion_update_and_readout_descend`
- Dependency: [D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness](../Dynamics/ControlledInterventionDescentUniqueness.md)
