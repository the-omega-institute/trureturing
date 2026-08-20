# Controlled Behavior Universality

## Abstract

Every finite controlled realization maps uniquely onto the complete behavior quotient.

**Theorem 1.1 (Controlled behavior has a universal minimal realization).**

$$\begin{gathered}\forall Y, U, O, W,\\{}[\operatorname{Fintype}(Y)], [\operatorname{Fintype}(W)],\\F: U \to \left(Y \to Y\right), q: Y \to O,\\r: Y \to W, G: U \to \left(W \to W\right), o: W \to O,\\\operatorname{Surjective}\left(r\right) \Rightarrow (\forall u\in U, r \circ F(u) = G(u) \circ r) \Rightarrow q = o \circ r \Rightarrow\\(\exists! h: W \to Z, \operatorname{Surjective}\left(h\right) \land \pi = h \circ r \land\\(\forall u\in U, h \circ G(u) = \overline{F}(u) \circ h) \land\\\overline{q} \circ h = o) \land \operatorname{card}(Z) \leq \operatorname{card}(W).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlled_behavior_universal_property` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite controlled state carrier with input-indexed updates and readout q. Let Z be the quotient by equality of every readout after every finite input word. Its projection, induced updates, and induced readout are defined directly from that behavior kernel.

For any finite realization W reached surjectively from Y, commuting with every update and with the readout, there is a unique surjective factor h from W to Z. It factors the canonical projection, intertwines every realized update, and preserves the readout. Surjectivity gives card(Z) at most card(W).

The factor is built from a right inverse of the realization map. Commutation along input words proves that different chosen preimages have equal complete behavior. Surjectivity of the canonical quotient projection proves surjectivity of h, while surjectivity onto W proves all equations and uniqueness pointwise.

Pinned Mathlib and Loogle supplied the exact declarations Setoid.quotientKerEquivRange and Fintype.card_le_of_surjective, both applied by the module. LeanSearch returned HTTP 404 for the shaped query, and local repository and pinned-library searches found no theorem packaging the complete universal property.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlled_behavior_universal_property`
