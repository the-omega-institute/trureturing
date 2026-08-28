# Single-Prime Thermal State

## Abstract

The single-prime thermal spectrum is a normalized geometric occupation law.

**Definition 1.1 (Single-prime thermal spectrum).**

Lean statement: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState`

*Formalization.* `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The countable diagonal model is represented by the occupation-number spectrum (1 - p^(-s)) p^(-s k) at mode k.

**Definition 1.2 (PMF associated with the thermal spectrum).**

Lean statement: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF`

*Formalization.* `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the regime p > 1 and s > 0, the spectrum is packaged as a countable probability mass function.

**Theorem 1.3 (Thermal spectral weights are nonnegative).**

$$\forall p \in \mathbb{N}, s \in \mathbb{R}, k \in \mathbb{N},\; \left(1 < p \land 0 < s\right) \Rightarrow 0 \le \operatorname{singlePrimeThermalState}\left(p, s, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p > 1 and s > 0, the ratio p^(-s) lies in (0, 1). Both factors in each diagonal weight are therefore nonnegative.

**Theorem 1.4 (Thermal spectral weights are normalized).**

$$\forall p \in \mathbb{N}, s \in \mathbb{R},\; \left(1 < p \land 0 < s\right) \Rightarrow \operatorname{tsum}\left(k, \operatorname{singlePrimeThermalState}\left(p, s, k\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_tsum_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric series with ratio p^(-s) sums to the inverse prefactor, so the diagonal spectrum has total mass one.

**Theorem 1.5 (The zero occupation slot).**

$$\operatorname{singlePrimeThermalState}\left(p, s, 0\right) = 1 - p^{{-s}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_zero_slot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k = 0 the geometric power is one, leaving exactly the vacuum weight 1 - p^(-s).

**Theorem 1.6 (The PMF realizes the thermal spectrum).**

$$\forall p \in \mathbb{N}, s \in \mathbb{R}, k \in \mathbb{N},\; \left(1 < p \land 0 < s\right) \Rightarrow \operatorname{pmfReal}\left(\operatorname{singlePrimeThermalPMF}\left(p, s\right), k\right) = \operatorname{singlePrimeThermalState}\left(p, s, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the real mass of the named PMF recovers the corresponding diagonal spectral weight at every occupation number.

**Theorem 1.7 (The PMF is geometric in the ratio parameter).**

$$\forall p \in \mathbb{N}, s \in \mathbb{R}, k \in \mathbb{N},\; \left(1 < p \land 0 < s\right) \Rightarrow \operatorname{pmfReal}\left(\operatorname{singlePrimeThermalPMF}\left(p, s\right), k\right) = (1 - p^{{-s}}) \operatorname{pow}\left(p^{{-s}}, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF_is_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The PMF has geometric ratio p^(-s), with success prefactor 1 - p^(-s), pointwise on the countable occupation space.

**Theorem 1.8 (Closed entropy of one thermal mode).**

$$\forall p \in \mathbb{N}, s \in \mathbb{R},\; \left(1 < p \land 0 < s\right) \Rightarrow \operatorname{countableEntropy}\left(\operatorname{singlePrimeThermalPMF}\left(p, s\right)\right) = -\operatorname{log}\left(1 - p^{{-s}}\right) + s \operatorname{log}\left(p\right) p^{{-s}} / 1 - p^{{-s}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermal_entropy_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reusable geometric Gibbs entropy theorem gives the closed Shannon formula for this diagonal mode; only p > 1 and s > 0 are needed.

**Theorem 1.9 (Modal thermal entropy adds over primes).**

$$\forall s \in \mathbb{R},\; 1 < s \Rightarrow \operatorname{countableEntropy}\left(\operatorname{zetaDist}\left(s\right)\right) = \operatorname{tsum}\left(p, \operatorname{countableEntropy}\left(\operatorname{singlePrimeThermalPMF}\left(p, s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.modal_thermal_entropy_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s > 1, the existing zeta diagonal PMF entropy equals the tsum of the named single-prime thermal mode entropies.

**Theorem 1.10 (Base greater than one is necessary).**

$$\neg \operatorname{tsum}\left(k, \operatorname{singlePrimeThermalState}\left(1, 1, k\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.base_gt_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the concrete base p = 1 and s = 1, every prefactor is zero and normalization fails.

**Theorem 1.11 (Positive temperature is necessary).**

$$\neg \operatorname{tsum}\left(k, \operatorname{singlePrimeThermalState}\left(2, 0, k\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.positive_temperature_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the concrete base p = 2 and temperature s = 0, the ratio is one, all weights vanish, and the total is not one.

**Theorem 1.12 (A negative-temperature spectrum is not summable).**

$$\neg \operatorname{Summable}\left(\operatorname{singlePrimeThermalState}\left(2, -1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.negative_temperature_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At p = 2 and s = -1, the weights are -2^k, giving a concrete non-summable divergent boundary case.

**Theorem 1.13 (Infinite temperature leaves the vacuum spectrum).**

$$\forall p \in \mathbb{N}, k \in \mathbb{N},\; 1 < p \Rightarrow \operatorname{Tendsto}\left(\operatorname{singlePrimeThermalState}\left(p, s, k\right), atTop, \operatorname{nhds}\left(\operatorname{if}\left(k = 0, 1, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_tendsto_infinite_temperature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed occupation number and p > 1, the spectrum tends as s tends to infinity to one at k = 0 and zero at every k > 0.

## References

- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.base_gt_one_is_necessary`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.modal_thermal_entropy_additive`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.negative_temperature_not_summable`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.positive_temperature_is_necessary`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF_apply`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalPMF_is_geometric`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_nonneg`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_tendsto_infinite_temperature`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_tsum_eq_one`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermalState_zero_slot`
- Truth anchor: `D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.singlePrimeThermal_entropy_eq`
