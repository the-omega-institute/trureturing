# Carrier Decay Threshold

## Abstract

A power-log counting bound gives the strict and endpoint summability thresholds.

**Definition 1.1 (The carrier counting function counts members below a cutoff).**

$$\forall A \in \operatorname{Set}\left(\mathbb{N}\right), n \in \mathbb{N},\; \operatorname{carrierCountingFunction}\left(A, n\right) = \operatorname{NatCount}\left((k \mapsto k \in A), n\right)$$

*Formalization.* `D5/S3/Analytic/Boundary/CarrierDecayThreshold.carrierCountingFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a set A of natural numbers, the counting function at n is Mathlib's natural predicate count below n. This fixes the source's cumulative count on the exact set carrier rather than replacing it by supplied shell data.

**Theorem 1.2 (Power-log counting decay gives both convergence regimes).**

$$\forall A \in \operatorname{Set}\left(\mathbb{N}\right), C \in \mathbb{R}, delta \in \mathbb{R}, beta \in \mathbb{R}, q \in \mathbb{R},\; \operatorname{EventuallyAtTop}\left((n \mapsto \operatorname{carrierCountingFunction}\left(A, n\right) \le \frac{C \cdot n^{delta}}{\operatorname{log}\left(n\right)^{\mathit{beta}}})\right) \Rightarrow \left(\left(delta < q \Rightarrow \operatorname{Summable}\left((n \mapsto \operatorname{indicator}\left(A, n\right) \cdot n^{-q})\right)\right) \land \left(\left(q = delta \land 1 < \mathit{beta}\right) \Rightarrow \operatorname{Summable}\left((n \mapsto \operatorname{indicator}\left(A, n\right) \cdot n^{-q})\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/CarrierDecayThreshold.carrier_decay_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a set of natural numbers whose counting function is eventually bounded by C times n to the delta divided by log n to the beta. The series of n to the minus q over A is summable whenever q is strictly larger than delta. At q equal to delta it is summable when beta is strictly larger than one.

The proof partitions A into exact base-two logarithmic fibers. Their cardinalities are bounded by the cumulative counting hypothesis, and every term in a positive-exponent shell is bounded using its lower dyadic endpoint. Above delta, logarithmic powers are absorbed by a smaller exponential gap and the shell bounds form a geometric series. At the endpoint the exponential factors cancel and leave a shifted p-series of exponent beta.

The statement does not assume delta or C is positive. When a negative delta makes the displayed majorant tend to zero, the eventual integer count forces A to be finite. The same argument handles delta zero at the logarithmic endpoint, so no unstated positivity restriction is added.

Repository, pinned-library, and Lean ecosystem searches found no exact owner. The proof directly applies the canonical natural count, exact summable partition, real p-series, logarithm-is-subpower, and geometric-series results. The indicator formulation is the series over the original set A; totalization at zero changes only one finite term.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/CarrierDecayThreshold.carrierCountingFunction`
- Truth anchor: `D5/S3/Analytic/Boundary/CarrierDecayThreshold.carrier_decay_threshold`
