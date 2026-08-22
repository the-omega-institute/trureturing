# Future Obligation Incompleteness

## Abstract

A noninjective interface misses a separating future Boolean obligation.

**Definition 1.1 (Collision obligation).**

Lean statement: `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.collisionObligation`

*Formalization.* `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.collisionObligation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a distinguished current object, the collision obligation is the Boolean readout that accepts exactly objects equal to it.

**Theorem 1.2 (A nonfaithful interface is incomplete for future obligations).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}V: \operatorname{Concept}\left(X, B\right),\\{}(\neg \operatorname{Injective}\left(V\right) \Rightarrow\\{}\exists x, y: X,\\{}x \neq y \land V(x) = V(y) \land\\{}\operatorname{collisionObligation}\left(x\right)(x) \neq \operatorname{collisionObligation}\left(x\right)(y) \land \neg (\exists factor: B \to Bool, \operatorname{collisionObligation}\left(x\right) = factor \circ V)) \land\\{}((\forall O: \operatorname{Concept}\left(X, Bool\right), \exists factor: B \to Bool, O = factor \circ V) \Rightarrow \operatorname{Injective}\left(V\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.nonfaithful_interface_future_incomplete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interface and every future Boolean obligation use the canonical concept-readout carrier. From noninjectivity, the pinned function theorem supplies distinct objects with the same interface value.

The public forward implication names the collision objects, states their interface equality, exposes separation by the collision obligation, and states directly that no Boolean factor through the interface recovers that obligation.

The independent reverse implication assumes factorization of every Boolean obligation and concludes injectivity. Its premise is local to that implication and is not assumed by the forward half.

The existing disclosure-defect theorem is applied to the explicit collision and separating obligation in both proof branches.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.collisionObligation`
- Truth anchor: `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.nonfaithful_interface_future_incomplete`
- Dependency: [D5/S0/Rewriting/Quotients/InformedDisclosureDefect](../../../S0/Rewriting/Quotients/InformedDisclosureDefect.md)
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
