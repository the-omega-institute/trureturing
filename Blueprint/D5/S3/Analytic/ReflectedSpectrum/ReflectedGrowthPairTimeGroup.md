# Reflected Growth Pair Time Group

## Abstract

The oriented reflected pair is a faithful multiplicative flow, while symmetric observation identifies opposite parameter directions.

**Definition 1.1 (Joint even-odd observation).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.orientedEvenOddObservation`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.orientedEvenOddObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint observer records both the reflection-invariant even channel and the oriented odd channel already defined by the frozen even-odd decomposition.

**Theorem 1.2 (The reflected pair is a one-parameter multiplicative group).**

$$\begin{aligned}\forall delta: \mathbb{R},\\\operatorname{reflectedGrowthPair}(delta, 0) = (1, 1) \land\\{\forall t_1: \mathbb{R}, t_2: \mathbb{R}, \operatorname{reflectedGrowthPair}(delta, t_1 + t_2) = \operatorname{reflectedGrowthPair}(delta, t_1) \cdot \operatorname{reflectedGrowthPair}(delta, t_2)} \land\\{\forall t: \mathbb{R}, \operatorname{reflectedGrowthPair}(delta, -t) = \operatorname{reflectedGrowthPair}(delta, t)^{-1}.}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_pair_time_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value at zero is the multiplicative identity, parameter addition becomes coordinatewise multiplication, and parameter reversal gives the inverse pair.

**Theorem 1.3 (A nonzero split makes the oriented pair faithful).**

$$\forall delta: \mathbb{R}, delta \neq 0 \Rightarrow \operatorname{Injective}(\operatorname{reflectedGrowthPair}(delta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_pair_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real exponential injectivity and the nonzero split recover the parameter from the first branch of the full pair.

**Theorem 1.4 (Symmetric observation loses parameter orientation).**

$$\forall delta: \mathbb{R}, \neg \operatorname{Injective}(\operatorname{reflectedGrowthSum}(delta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_sum_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen evenness theorem supplies the explicit collision between parameter values one and minus one, so the branch-forgetting readout is never injective.

**Theorem 1.5 (Even and odd channels together restore orientation).**

$$\forall delta: \mathbb{R}, delta \neq 0 \Rightarrow \operatorname{Injective}(\operatorname{orientedEvenOddObservation}(delta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.oriented_even_odd_observation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact branch reconstruction converts equality of joint observations into equality of the positive-rate exponential branch, which recovers the parameter for a nonzero split.

**Theorem 1.6 (Oriented time recovery and symmetric time loss).**

$$\begin{aligned}\forall delta: \mathbb{R}, delta \neq 0 \Rightarrow (\\\operatorname{Injective}(\operatorname{reflectedGrowthPair}(delta)) \land\\\neg \operatorname{Injective}(\operatorname{reflectedGrowthSum}(delta)) \land\\\operatorname{Injective}(\operatorname{orientedEvenOddObservation}(delta)) \land\\\forall t: \mathbb{R}, \operatorname{reflectedGrowthPair}(delta, -t) = \operatorname{reflectedGrowthPair}(delta, t)^{-1}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.oriented_time_recovery_symmetric_time_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The packaged theorem separates three facts: the full pair is faithful, the symmetric quotient loses orientation, and adjoining the odd channel restores faithful observation. Negative parameter is represented by the inverse group element.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.orientedEvenOddObservation`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.oriented_even_odd_observation_injective`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.oriented_time_recovery_symmetric_time_loss`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_pair_injective`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_pair_time_group`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.reflected_growth_sum_not_injective`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition](ReflectedGrowthPairEvenOddDecomposition.md)
