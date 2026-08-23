# Price Cannot Carry All Micro-Information

## Abstract

A price strictly coarser than a joint micro-readout misses a target, while a faithful price carries every target determined by that readout.

**Theorem 1.1 (A strictly coarser price misses a joint target).**

$$\forall X \in Type, Price \in Type, C1 \in Type, C2 \in Type, price \in X \to Price, q1 \in X \to C1, q2 \in X \to C2,\; \operatorname{StrictRefinement}\left(price, \operatorname{conceptJoin}\left(q1, q2\right)\right) \Rightarrow \left(\exists target \in X \to C1 \times C2,\; \operatorname{Refines}\left(target, \operatorname{conceptJoin}\left(q1, q2\right)\right) \land \left(\neg \operatorname{Refines}\left(target, price\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.strictly_coarser_price_misses_some_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint readout itself supplies the missing target. It is determined by the joint information through the identity factor map.

Strict coarseness says that this joint readout cannot factor through the price. The target is therefore explicit: no cardinality or choice argument is needed to find information that the price fails to carry.

**Lemma 1.2 (A faithful price carries every joint target).**

$$\forall X \in Type, Price \in Type, C1 \in Type, C2 \in Type, Target \in Type, price \in X \to Price, q1 \in X \to C1, q2 \in X \to C2, target \in X \to Target,\; \left(\operatorname{Refines}\left(\operatorname{conceptJoin}\left(q1, q2\right), price\right) \land \operatorname{Refines}\left(target, \operatorname{conceptJoin}\left(q1, q2\right)\right)\right) \Rightarrow \operatorname{Refines}\left(target, price\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.faithful_price_carries_every_join_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the joint readout factors through the price, every target already determined by that readout also factors through the price. Composing the two factor maps proves that a faithful price loses none of the targets supported by the joint micro-information.

**Lemma 1.3 (The first-coordinate price is strictly coarser).**

$$\operatorname{StrictRefinement}\left(coordinatePrice, \operatorname{conceptJoin}\left(coordinatePrice, snd\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.coordinate_price_strictly_coarser` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a pair of Boolean coordinates, the coordinate price retains only the first coordinate. Projection from the joint readout recovers that price, so the joint readout refines it.

The states (false, false) and (false, true) have the same price but different second coordinates. Hence the full joint readout cannot factor back through the price, making the refinement genuinely strict.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.coordinate_price_strictly_coarser`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.faithful_price_carries_every_join_target`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.strictly_coarser_price_misses_some_target`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/StrictRefinementCapability](../StrictRefinementCapability.md)
