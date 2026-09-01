# Reflected Growth Pair Even-Odd Decomposition

## Abstract

Even and odd reflected channels separate invariant magnitude from time orientation.

**Definition 1.1 (The reflection-invariant even channel).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.evenObservation`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.evenObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The even channel averages the two frozen reflected branches. It forgets which branch expands and which contracts while retaining their reflection-invariant magnitude.

**Definition 1.2 (The oriented odd channel).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.oddObservation`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.oddObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The odd channel is half the branch difference. Parameter reversal changes its sign, so it records the orientation erased by the symmetric sum.

**Theorem 1.3 (Even and odd channels reconstruct the reflected pair).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, \operatorname{evenObservation}(delta, -t) = \operatorname{evenObservation}(delta, t) \land \operatorname{oddObservation}(delta, -t) = -\operatorname{oddObservation}(delta, t) \land \operatorname{evenObservation}(delta, t) + \operatorname{oddObservation}(delta, t) = \operatorname{positiveRateBranch}(delta, t) \land \operatorname{evenObservation}(delta, t) - \operatorname{oddObservation}(delta, t) = \operatorname{negativeRateBranch}(delta, t) \land \operatorname{evenObservation}(delta, t)^{2} - \operatorname{oddObservation}(delta, t)^{2} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.reflected_growth_pair_even_odd_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The even channel is invariant under parameter reversal and the odd channel is anti-invariant. Their sum and difference recover the two oriented exponential branches exactly.

The frozen reciprocal product becomes the Lorentzian identity E squared minus O squared equals one. This is a finite scalar identity and does not assert a completed-zeta realization.

**Theorem 1.4 (The odd channel vanishes only at zero split or zero parameter).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, \operatorname{oddObservation}(delta, t) = 0 \iff delta = 0 \lor t = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.odd_observation_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oriented channel loses all signal exactly when the reflected split is absent or when the observation is taken at the reflection center.

**Theorem 1.5 (Positive split and positive parameter give positive odd orientation).**

$$\forall delta: \mathbb{R}, t: \mathbb{R}, 0 < delta \land 0 < t \Rightarrow 0 < \operatorname{oddObservation}(delta, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.odd_observation_positive_of_forward_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen forward-orientation theorem orders the expanding branch above the contracting branch. Their half-difference is therefore positive.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.evenObservation`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.oddObservation`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.odd_observation_eq_zero_iff`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.odd_observation_positive_of_forward_orientation`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition.reflected_growth_pair_even_odd_decomposition`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum](../Adelic/ReflectedGrowthPairSecondOrderSpectrum.md)
