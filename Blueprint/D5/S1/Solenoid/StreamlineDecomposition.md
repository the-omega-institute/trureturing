# Canonical Streamline Decomposition

## Abstract

Every continuous solenoid path has a unique base-normalized real lift and a constant hidden offset.

**Definition 1.1 (The visible phase has a canonical representative).**

$$rep(\gamma)= \operatorname{IcoRep}(\pi(\gamma(0)))\in [0, 1)$$

*Formalization.* `D5/S1/Solenoid/StreamlineDecomposition.baseRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition chooses the unique real representative in the half-open interval from zero to one of the path's visible phase at the normalization time. This removes the integer ambiguity in a real lift of the additive circle.

**Theorem 1.2 (Every solenoid path has a unique normalized streamline).**

$$\forall \gamma: C(\mathbb{R}, \mathcal S), t0: \mathbb{R},,\ \exists! r, k,\ r(0)= rep(\gamma) \land k\in \ker(\pi) \land \forall t,\ \gamma(t)= realFlow(r(t))+ k.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/StreamlineDecomposition.existsUnique_normalized_streamline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's covering-lift theorem constructs the unique continuous real lift of the visible projection after fixing its value at zero. Subtracting the induced real flow from the original path gives a continuous kernel-valued motion.

At modulus m, every point of that motion lies in the finite m-torsion subset of the additive circle. A continuous image of the connected real line inside this discrete finite set is constant. Coordinate extensionality gives one time-independent hidden solenoid element; covering-lift uniqueness and group cancellation give uniqueness of the complete pair.

The pinned library was searched first. AddCircle.isCoveringMap_coe, IsCoveringMap.existsUnique_continuousMap_lifts, AddCircle.finite_torsion, Set.Finite.isDiscrete, and IsPreconnected.constant_of_mapsTo supply the general steps. No library result packages their universal-solenoid assembly.

**Theorem 1.3 (A translated real flow has a nonzero hidden offset).**

$$\exists! r, k,\ r(0)= rep(translated) \land \forall t,\ realFlow(t)+ hiddenUnit= realFlow(r(t))+ k \land r(0)\neq r(1) \land k\neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/StreamlineDecomposition.translated_realFlow_has_nonzero_hidden_offset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate the real-flow path by its time-one value. That value has visible phase zero but is nonzero at the modulus-two coordinate, where it is the class of one half. The unique normalized data therefore contain both the nonconstant identity lift and a genuinely nonzero constant hidden offset.

## References

- Truth anchor: `D5/S1/Solenoid/StreamlineDecomposition.baseRepresentative`
- Truth anchor: `D5/S1/Solenoid/StreamlineDecomposition.existsUnique_normalized_streamline`
- Truth anchor: `D5/S1/Solenoid/StreamlineDecomposition.translated_realFlow_has_nonzero_hidden_offset`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../Dynamics/UniversalSolenoid.md)
