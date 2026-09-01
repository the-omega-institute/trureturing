# Pair-Calibrated Second-Magnus Observability

## Abstract

Pair-adapted samples recover four times the finite holonomy energy.

**Theorem 1.1 (Exact calibrated reverse observability).**

$$(\operatorname{Injective}\left(omega\right) \land \forall p, C\left(p, p\right) = 0) \Rightarrow \operatorname{Ecal}\left(omega, C\right) = 4 \times \operatorname{Ehol}\left(C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability.pair_calibrated_second_magnus_energy_eq_four_holonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For injective frequencies and a curvature field with zero diagonal, each ordered pair is sampled at its own half-turn time separation.

The resulting calibrated second-Magnus energy is exactly four times the finite holonomy energy. The clocks remain pair dependent, so a family-wide common-window frame bound is still separate.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability.pair_calibrated_second_magnus_energy_eq_four_holonomy`
- Dependency: [D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy](FiniteHolonomyEnergy.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](SecondMagnusSwapCurvature.md)
