# Explicit density of circles without opposite-pair adjacencies

## Abstract

Explicit density of circles without opposite-pair adjacencies

**Theorem 1.1 (Explicit density of circles without opposite-pair adjacencies).**

$$\forall r \in \mathrm{Nat},\; (12 \le r) \Rightarrow (\frac{4 \cdot r^{2} - 11 \cdot r + 9}{3 \cdot \left(2 \cdot r - 1\right) \cdot \left(2 \cdot r - 3\right)} \le \frac{\mathrm{card}\left(\mathrm{noAdjacency}\left(r\right)\right)}{\mathrm{factorial}\left(2 \cdot r - 1\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.no_adjacency_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NoAdjacency(r) is the actual subset of circles(alphabet(r)) in which no designated opposite pair is adjacent. Every count and factorial in the displayed ratios is interpreted in the rationals.

The actual degree-zero through degree-three intersection counts give the third odd Bonferroni truncation on the original paired circle inventory. Dividing by its positive cardinality (2r-1)! gives the density lower bound (4r^2-11r+9)/(3(2r-1)(2r-3)).

These are simultaneous contractions of distinct original pairs on one oriented circle. In particular the pairwise intersection count is not the product of its marginal counts. This estimate is consumed together with the unconditional residual zero-block bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate.no_adjacency_lower_bound`
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedCircleEvents](PairedCircleEvents.md)
