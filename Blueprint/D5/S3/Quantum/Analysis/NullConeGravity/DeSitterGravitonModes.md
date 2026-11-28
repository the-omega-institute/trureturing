# De Sitter transverse-traceless graviton modes

## Abstract

The de Sitter tensor mode equation, normalized four-dimensional solutions and dimension selection.

The tensor equation concerns individual bulk Fourier polarizations. Appendix B.2 of Satishchandran and Sorce describes the Minkowski characteristic graviton reference.

**Definition 1.1 (Tensor rescaling exponent).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonKappa`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonKappa` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Half the tensor kinetic exponent, κ = (D − 2)/2.

**Theorem 1.2 (Exact tensor rescaling).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_rescaled_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_rescaled_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 2, H > 0 and t < 0, set Ω = −1/(Ht) and v = Ω^κ h. The operator (Ω^(D − 2)h′)′ + Ω^(D − 2)k²h equals Ω^κ[v″ + (k² − κ(κ + 1)/t²)v]. The identity uses differentiability of h at negative times and of its derivative at t.

**Theorem 1.3 (Minimally coupled scalar potential).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_scalar_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_scalar_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 4, H > 0 and t < 0, the scalar conformal mass shift at zero bare mass and curvature coupling yields the same potential k² − κ(κ + 1)/t².

**Definition 1.4 (Four-dimensional Bunch–Davies mode).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4GravitonBDMode`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4GravitonBDMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply exp(−ikt) by 1 − i/(kt) and divide by √(2k).

**Theorem 1.5 (Exact mode equation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_mode_solves_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_mode_solves_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For k > 0 and t < 0 the mode satisfies v″ + (k² − 2/t²)v = 0.

**Theorem 1.6 (Canonical Wronskian).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_wronskian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_wronskian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For k > 0 and t < 0, v times the conjugate of v′ minus the conjugate of v times v′ equals i.

**Theorem 1.7 (Squared metric mode amplitude).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_power`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For H > 0, k > 0 and t < 0, |v/Ω|² = H²(1 + k²t²)/(2k³).

**Theorem 1.8 (Superhorizon power).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_superhorizon_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_superhorizon_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For H > 0 and k > 0 the squared amplitude tends to H²/(2k³) as t approaches zero from below. Multiplying the limit by k³ gives a scale-independent amplitude.

**Definition 1.9 (Tensor polarization space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.GravitonTT`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.GravitonTT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use the existing symmetric trace-free space on a screen of dimension D − 2.

**Definition 1.10 (Tensor polarization count).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarizationCount`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarizationCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use the natural-number formula (D − 2)(D − 1)/2 − 1.

**Theorem 1.11 (Equivalent screen count).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarization_eq_screenSTF`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarization_eq_screenSTF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The count equals the existing screen dimension D(D − 3)/2.

**Theorem 1.12 (Rank of the trace-free screen).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.finrank_gravitonTT`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.finrank_gravitonTT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 2 the screen has rank (D − 2)(D − 1)/2 − 1. The two-dimensional spacetime boundary has an empty screen and rank zero.

**Theorem 1.13 (Polarizations in three, four and five dimensions).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_polarizations_three_four_five`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_polarizations_three_four_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The three counts are zero, two and five, respectively.

**Theorem 1.14 (Weyl tidal coordinates in dimension four).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton4_weyl_screen_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton4_weyl_screen_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Half the real and imaginary parts of the complex Weyl tide are the first diagonal and off-diagonal entries of the real trace-free screen tide.

**Theorem 1.15 (Propagation threshold).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_propagating_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_propagating_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The tensor polarization count is positive exactly when D ≥ 4.

**Theorem 1.16 (Gravity and scalar summability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.scalar_nullDiamond_and_propagating_gravity_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.scalar_nullDiamond_and_propagating_gravity_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The conjunction of D ≥ 4 and leading null-diamond angular weight summability holds exactly in dimensions four and five.

**Theorem 1.17 (Selection by Maxwell invariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_nullDiamond_and_conformalMaxwell`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_nullDiamond_and_conformalMaxwell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Intersect the gravity and scalar summability window with Maxwell invariance at every positive conformal scale. The intersection consists of dimension four.

**Theorem 1.18 (Selection by Proca curvature cancellation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_graviton_nullDiamond_and_procaConformal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_graviton_nullDiamond_and_procaConformal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A positive tensor polarization count, scalar leading-weight summability and zero transverse Proca curvature coefficient occur together exactly in dimension four.

**Theorem 1.19 (Joint Weyl, scalar, Maxwell and Hodge selection).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.grand_unification_unique_dimension_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.grand_unification_unique_dimension_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For D ≥ 3, positive Weyl rank, summable scalar leading weights, invariant Maxwell weight at every positive scale, and Hodge complementary degree two for 2-forms hold together exactly when D = 4.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.GravitonTT`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4GravitonBDMode`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_mode_solves_ode`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_power`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_superhorizon_limit`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds4_graviton_bd_wronskian`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_rescaled_ode`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.ds_graviton_tt_scalar_potential`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.finrank_gravitonTT`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.grand_unification_unique_dimension_four`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton4_weyl_screen_coordinates`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonKappa`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarizationCount`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.gravitonPolarization_eq_screenSTF`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_polarizations_three_four_five`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.graviton_propagating_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.scalar_nullDiamond_and_propagating_gravity_iff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_graviton_nullDiamond_and_procaConformal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.unique_dimension_four_of_nullDiamond_and_conformalMaxwell`
- Dependency: [D5/S3/Geometry/Lorentz/DimensionSelection4D](../../../Geometry/Lorentz/DimensionSelection4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](../../../Geometry/Lorentz/WeylNullScreen.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D](ConformalMaxwellSelection4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold](NullDiamondDimensionThreshold.md)
