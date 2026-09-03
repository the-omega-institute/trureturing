# Carrier-Decay Threshold

## Abstract

A dyadic counting bound with logarithmic decay implies the sharp power-series threshold.

**Theorem 1.1 (Dyadic carrier decay gives power-series summability).**

$$\forall A \in \mathbb{N} \to Prop, C \in \mathbb{R}, delta \in \mathbb{R}, beta \in \mathbb{R}, q \in \mathbb{R},\; \left(\left(\neg A\left(0\right)\right) \land \left(0 \le C \land \left(0 \le \delta \land \left(0 \le \beta \land \left(\left(\exists kzero \in \mathbb{N},\; \forall k \in \mathbb{N},\; kzero \le k \Rightarrow \operatorname{countBelow}\left(A, 2^{k + 1}\right) \cdot \left(2^{{-\delta}}\right)^{k} \le \frac{C}{\left(k + 1\right)^{\beta}}\right) \land \left(\delta < q \lor \left(q = \delta \land 1 < \beta\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Summable}\left((n: \operatorname{carrierSubtype}\left(A\right) \mapsto n^{{-q}})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/CarrierDecayThreshold.carrier_decay_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a carrier of positive natural numbers. Its counting function N_A(X) is the number of carrier elements strictly below X. Assume that, from some dyadic scale onward, the displayed normalized count is bounded by a logarithmic power.

Partition A into the shells with base-two logarithm k. Every positive integer belongs to exactly one shell, the kth shell is finite, and each of its terms is at most 2 to the power -qk.

For q greater than delta, the shell sums are eventually dominated by a geometric series. At q equal to delta, they are dominated by the shifted p-series with exponent beta, which converges for beta > 1.

The source's sufficiently-large real-variable bound is stated here in its direct dyadic form; fixed factors from log 2 and the endpoint 2^(k+1) are absorbed into C. The formal statement also excludes zero from A and requires C, delta, and beta to be nonnegative, preventing totalized negative powers or sign-degenerate bounds.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/CarrierDecayThreshold.carrier_decay_threshold`
