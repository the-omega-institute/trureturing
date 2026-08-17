# Itinerary Completion

## Abstract

Kernel classes, complete itineraries, and compatible finite words agree dynamically.

**Theorem 1.1 (Finite itinerary completion stabilizes).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)],\\tau: Y \to Y, q: Y \to O,\\\exists ez: Zq \equiv \operatorname{Iq}\left(Y\right), \operatorname{Semiconj}\left(ez, Uq, Ui\right) \land\\\exists el: \operatorname{Iq}\left(Y\right) \equiv \operatorname{CompatibleLimit}\left(tau, q\right), \operatorname{Semiconj}\left(el, Ui, Ul\right) \land\\\exists m \in \mathbb{N}, \exists em: \operatorname{Iq}\left(Y\right) \equiv \operatorname{X}\left(m\right),\\\operatorname{toFun}\left(em\right) = \operatorname{coordinateProjection}\left(m\right) \land \operatorname{Bijective}\left(\operatorname{coordinateProjection}\left(m\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ItineraryCompletion.itinerary_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state type with deterministic update tau and readout q. Its complete itinerary records every future readout. The type Zq is the quotient of Y by equality of complete itineraries, while Iq is the range of the itinerary map. Each finite layer Xm is the range of the readout word through m.

The compatible-family limit consists of one realized word at every depth, with later words restricting to earlier words. The theorem gives an equivalence from Zq to Iq and another from Iq to this limit. Both equivalences intertwine their update maps, which records the asserted dynamical naturality.

For each distinguishable pair of states, choose one differing time. The supremum of these times over the finite state-pair type is a finite completion depth. Equality of words there forces equality of complete itineraries. It follows that coordinate projection from Iq to that finite layer is bijective, and every compatible family is represented by its stable coordinate.

Pinned Mathlib and Loogle supply the exact kernel-range equivalence Setoid.quotientKerEquivRange. Equiv.ofBijective packages the coordinate and compatible-family bijections, and Finset.le_sup bounds each chosen distinguishing time. LeanSearch returned HTTP 404 for the shaped searches, and repository search found no equal or stronger finite-completion result.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ItineraryCompletion.itinerary_completion`
