# Dynamic Indistinguishability Coordinatewise

## Abstract

Dynamic indistinguishability on an independent finite product is exactly coordinatewise, and factorwise action is necessary.

**Theorem 1.1 (Dynamic indistinguishability is coordinatewise).**

$$\forall k \in \mathbb{N}, X \in \operatorname{Fin}(k) \to \operatorname{Type}, O \in \operatorname{Fin}(k) \to \operatorname{Type}, F \in \pi i:\operatorname{Fin}(k), X(i) \to X(i), q \in \pi i:\operatorname{Fin}(k), X(i) \to O(i), x \in \operatorname{ProductState}(X), y \in \operatorname{ProductState}(X),\; \operatorname{DynamicIndistinguishable}(\operatorname{coordinateUpdate}(F), \operatorname{coordinateReadout}(q), x, y) \Leftrightarrow \left(\forall i \in \operatorname{Fin}(k),\; \operatorname{DynamicIndistinguishable}(F(i), q(i), x(i), y(i))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.dynamic_indistinguishability_iff_coordinatewise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type and dependent state and output families, the update and readout are formed by applying their local maps at each coordinate.

Equality of every global readout at every time implies equality at each coordinate. Conversely, coordinatewise equality at every time gives equality of the dependent output functions by function extensionality.

The finite index may be empty; no primality, prime-power, finiteness of carriers, injectivity, surjectivity, or nonconstant readout is assumed.

**Theorem 1.2 (Factorwise readout is necessary).**

$$\operatorname{UpdateActsFactorwise}(id) \land \left(\left(\neg \operatorname{ReadoutActsFactorwise}(crossBooleanReadout)\right) \land \left(\neg \left(\operatorname{DynamicIndistinguishable}(id, crossBooleanReadout, booleanStateA, booleanStateB) \Leftrightarrow \left(\forall i \in \operatorname{Fin}(2),\; \operatorname{DynamicIndistinguishable}(id, constantFalse, booleanStateAi, booleanStateBi)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.readout_factorwise_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a two-coordinate Boolean product, the identity update and constant local readouts make every coordinate pair locally indistinguishable.

A cross-coordinate readout that repeats coordinate zero globally separates two such states at time zero. Thus the iff fails when the readout does not act factorwise.

**Theorem 1.3 (Factorwise update is necessary).**

$$\operatorname{ReadoutActsFactorwise}(firstCoordinateReadout) \land \left(\left(\neg \operatorname{UpdateActsFactorwise}(hiddenCrossUpdate)\right) \land \left(\neg \left(\operatorname{DynamicIndistinguishable}(hiddenCrossUpdate, firstCoordinateReadout, hiddenStateA, hiddenStateB) \Leftrightarrow \left(\forall i \in \operatorname{Fin}(2),\; \operatorname{DynamicIndistinguishable}(id, first, hiddenStateAi, hiddenStateBi)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.update_factorwise_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a two-coordinate product of Boolean pairs, the first-coordinate readout is factorwise and the local updates are identities.

A cross-coordinate update copies a hidden second component into the other coordinate. The local relations remain true, but the global relation fails after one step, so factorwise updating is necessary.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.dynamic_indistinguishability_iff_coordinatewise`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.readout_factorwise_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.update_factorwise_is_necessary`
