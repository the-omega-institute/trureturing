# Finite Fourier Magnus Commutator

## Abstract

Expand a finite Fourier generator commutator with the frozen slot kernel.

**Theorem 1.1 (Fourier commutator expansion).**

$$\operatorname{comm}\left(\operatorname{HG}\left(t1\right), \operatorname{HG}\left(t2\right)\right) = \sum_{p, q} \operatorname{K}\left(omega\left(p\right), omega\left(q\right), t1, t2\right) \times G\left(p\right)G\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFourierMagnusCommutator.finite_fourier_algebra_generator_commutator_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family in a complex associative algebra, the commutator of the Fourier syntheses at two times is the double sum of ordered algebra products weighted by the alternating slot kernel.

This closes the finite algebraic coefficient bridge to a second Magnus term. It does not construct a time-ordered exponential, a Bochner integral, or an infinite-frequency operator.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFourierMagnusCommutator.finite_fourier_algebra_generator_commutator_expansion`
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](SecondMagnusSwapCurvature.md)
