# Conditional means on a three-bit cube

## Abstract

A conditional mean criterion for centered upper-event signs on a three-bit cube.

**Theorem 1.1 (Every upper event has nonpositive centered sum).**

$$\forall p, h, \operatorname{AntitoneFiberMeans}(p, h) \Rightarrow \forall U, \operatorname{IsUpperSet}(U) \Rightarrow \operatorname{CenteredSum}(p, h, U) \leq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans.centered_sum_nonpos_of_antitone_fiber_means` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any probability mass function on the pointwise ordered three-bit cube and any real score. For each coordinate subset, compare the conditional score at all comparable pairs of positive-mass fibers. AntitoneFiberMeans denotes these comparisons. CenteredSum is the probability-weighted sum of the score minus its overall mean on the indicated upper set. A coordinate-face comparison gives the sign for upper sets contained in or containing an upper face. For the majority event, exchanging one singleton for one doubleton reduces the sign to the upper-face sign and two point comparisons.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans.centered_sum_nonpos_of_antitone_fiber_means`
