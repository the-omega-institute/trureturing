# Third finite Bonferroni bound on one event space

## Abstract

Third finite Bonferroni bound on one event space

**Theorem 1.1 (Third finite Bonferroni bound on one event space).**

$$\forall alpha \in \mathrm{Type},\; \forall iota \in \mathrm{Type},\; \forall X \in \mathrm{Finset}\left(alpha\right),\; \forall I \in \mathrm{Finset}\left(iota\right),\; \forall E \in \mathrm{Predicates}\left(iota, alpha\right),\; \sum_{p\in\mathrm{range}\left(4\right)}(\left(0 - 1\right)^{p} \cdot \sum_{T\in\mathrm{powersetCard}\left(I, p\right)}(\mathrm{card}\left(\mathrm{Intersection}\left(X, E, T\right)\right))) \le \mathrm{card}\left(\mathrm{Avoid}\left(X, E, I\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/FiniteEventBonferroniThree.bonferroni_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both carriers have decidable equality, with finite sets X and I. E assigns a predicate on alpha to each iota. Intersection(X,E,T) filters X by all events indexed by T; Avoid(X,E,I) filters by failure of every event indexed by I.

For each point of one finite space, count the events that occur. The degree-p intersection memberships are exactly the p-element subsets of those events. The alternating binomial identity gives a nonpositive third odd truncation when any event occurs, and gives one when no event occurs.

Summing this pointwise inequality gives the third Bonferroni lower bound for the number avoiding every event. The actual paired circular intersections supply its moments. No joint law is replaced by a product of marginal counts.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/FiniteEventBonferroniThree.bonferroni_three`
