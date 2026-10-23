# Ordered noncrossing matchings and boundary labels

## Abstract

Ordered noncrossing matchings and boundary labels.

**Definition 1.1 (Ordered noncrossing matchings and boundary labels).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \operatorname{Compatible}\left(M, y\right) \Leftrightarrow \left(\forall a \in \operatorname{Fin}\left(m\right),\; \operatorname{Apply}\left(y, \operatorname{CastSucc}\left(a\right)\right) = \operatorname{Apply}\left(y, \operatorname{Succ}\left(\operatorname{Partner}\left(M, a\right)\right)\right) \land \operatorname{Apply}\left(y, \operatorname{Succ}\left(a\right)\right) = \operatorname{Apply}\left(y, \operatorname{CastSucc}\left(\operatorname{Partner}\left(M, a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matching is a fixed-point-free involution of the ordered endpoints with no strictly alternating arcs. The label compatibility equations identify opposite sides of every pair. The boundary potential is zero for incompatible labels and otherwise is the product of the prescribed real weight ratios over opening endpoints.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.Compatible`
