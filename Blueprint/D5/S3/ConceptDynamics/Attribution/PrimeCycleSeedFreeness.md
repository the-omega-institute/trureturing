# Prime-cycle test profiles

## Abstract

Prime divisibility of a complete grid denominator forces a free seed action.

**Theorem 1.1 (Freeness from prime divisibility).**

$$\forall I S m w f, \operatorname{PrimeDivisibility}\left(I, m\right) \land \operatorname{Positive}\left(w\right) \land \operatorname{Calibrated}\left(m, w, f\right) \land \operatorname{Equivariant}\left(f\right) \Rightarrow \operatorname{FreeAction}\left(I, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness.free_of_prime_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I and S be finite types, with decidable equality on I. The full permutation group of I acts on S. Suppose every prime at most the number of labels divides the natural denominator m. Let w be a strictly positive real weight on each seed. For every natural profile of total m, let f assign each seed a label. Exact calibration means the sum of the weights assigned to each label is its profile coordinate in these units. The readout is equivariant when the same permutation acts on the profile and the seed.

If a seed stabilizer were nontrivial, Cauchy's theorem supplies an element of prime order p. Each nontrivial cycle of that element has length p. Choose the profile that takes value m divided by p on one such cycle and zero elsewhere. The element fixes the seed and the profile. Equivariance forces the seed to return a fixed label outside the chosen cycle. The weight of the seed is positive while the calibrated mass of that label is zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness.free_of_prime_divisibility`
