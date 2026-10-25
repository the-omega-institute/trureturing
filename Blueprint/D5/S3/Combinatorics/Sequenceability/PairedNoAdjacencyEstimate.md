# Explicit density of circles without opposite-pair adjacencies

## Abstract

Explicit density of circles without opposite-pair adjacencies

**Theorem 1.1 (Third finite Bonferroni bound on one event space).**

$$\forall alpha \in \mathrm{Type},\; \forall iota \in \mathrm{Type},\; \forall X \in \mathrm{Finset}\left(alpha\right),\; \forall I \in \mathrm{Finset}\left(iota\right),\; \forall E \in \mathrm{Predicates}\left(iota, alpha\right),\; \sum_{p\in\mathrm{range}\left(4\right)}(\left(0 - 1\right)^{p} \cdot \sum_{T\in\mathrm{powersetCard}\left(I, p\right)}(\mathrm{card}\left(\mathrm{Intersection}\left(X, E, T\right)\right))) \le \mathrm{card}\left(\mathrm{Avoid}\left(X, E, I\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.bonferroni_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both carriers have decidable equality, with finite sets X and I. E assigns a predicate on alpha to each iota. Intersection(X,E,T) filters X by all events indexed by T; Avoid(X,E,I) filters by failure of every event indexed by I.

For each point of one finite space, count the events that occur. The degree-p intersection memberships are exactly the p-element subsets of those events. The alternating binomial identity gives a nonpositive third odd truncation when any event occurs, and gives one when no event occurs.

Summing this pointwise inequality gives the third Bonferroni lower bound for the number avoiding every event. The actual paired circular intersections supply its moments. No joint law is replaced by a product of marginal counts.

**Theorem 1.2 (Explicit density of circles without opposite-pair adjacencies).**

$$\forall r \in \mathrm{Nat},\; (12 \le r) \Rightarrow (\frac{4 \cdot r^{2} - 11 \cdot r + 9}{3 \cdot \left(2 \cdot r - 1\right) \cdot \left(2 \cdot r - 3\right)} \le \frac{\mathrm{card}\left(\mathrm{noAdjacency}\left(r\right)\right)}{\mathrm{factorial}\left(2 \cdot r - 1\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.no_adjacency_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NoAdjacency(r) is the actual subset of circles(alphabet(r)) in which no designated opposite pair is adjacent. Every count and factorial in the displayed ratios is interpreted in the rationals.

pointwise_three bounds the alternating binomial sum for the number of events occurring at each point. intersection_moment counts those binomial coefficients by actual event intersections. Summing yields bonferroni_three; simultaneous-pair contraction counts then give no_adjacency_lower_bound on the same circle inventory.

The actual degree-zero through degree-three intersection counts give the third odd Bonferroni truncation on the original paired circle inventory. Dividing by its positive cardinality (2r-1)! gives the density lower bound (4r^2-11r+9)/(3(2r-1)(2r-3)).

These are simultaneous contractions of distinct original pairs on one oriented circle. In particular the pairwise intersection count is not the product of its marginal counts. This estimate is consumed together with the unconditional residual zero-block bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.bonferroni_three`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.no_adjacency_lower_bound`
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedCircleEvents](PairedCircleEvents.md)
