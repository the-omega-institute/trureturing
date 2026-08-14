# Bernoulli Bridge Variance

## Abstract

The Bernoulli bridge variance is the product of its distances from the endpoints.

**Theorem 1.1 (The Bernoulli bridge variance is t times one minus t).**

$$\forall t\in[0, 1],\ \operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, t)) = t(1 - t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge at t is the Bernoulli probability measure placing mass t at one and mass one minus t at zero. The identity observable therefore has mean t.

Mathlib states the corresponding binomial variance formula only as an unproved placeholder in this pinned revision. The Lean proof instead uses the proved Bernoulli integral formula and the definition of variance, then finishes by ring normalization.

This closes only the exact bridge-variance identity. The source's numerical five-point fit and its broader interpretive comparisons remain unresolved.

**Theorem 1.2 (The bridge variance vanishes at the endpoints and is one quarter at the midpoint).**

$$\operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, 0)) = 0 \land \operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, 1)) = 0 \land \operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, \frac{1}{2})) = \frac{1}{4}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_endpoints_and_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution in the exact variance identity gives both zero endpoint values and the displayed midpoint value without numerical approximation.

**Theorem 1.3 (The bridge variance is at most one quarter).**

$$\forall t\in[0, 1],\ \operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, t)) \leq \frac{1}{4}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Completing the square bounds t times one minus t by one quarter on the unit interval.

**Theorem 1.4 (The bridge variance reaches one quarter exactly at the midpoint).**

$$\forall t\in[0, 1],\ (\operatorname{Var}(\operatorname{id}, \operatorname{Ber}(1, 0, t)) = \frac{1}{4} \Leftrightarrow t = \frac{1}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_eq_quarter_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the completed-square bound forces t to equal one half, and direct substitution proves the converse.

## References

- Truth anchor: `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance`
- Truth anchor: `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_endpoints_and_midpoint`
- Truth anchor: `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_eq_quarter_iff`
- Truth anchor: `D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter`
