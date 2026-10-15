# Finite-Frequency Ordered-Simplex Coercivity

## Abstract

A finite nonresonant frequency family has a uniform ordered-simplex energy bound.

**Theorem 1.1 (Finite-family lower coercivity).**

$$0 < delta \land \operatorname{gapFloor}\left(delta, omega\right) \Rightarrow (horizon^{2} - \frac4 / delta^{2}) \times coefficientEnergy \leq \operatorname{Esimp}\left(omega, coefficient, horizon\right) \leq horizon^{2} \times coefficientEnergy$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_ordered_simplex_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive minimum gap gives one common lower response bound for every member of a finite frequency family.

The result is finite and analytic; it does not construct a Weil test or supply a zero-side or Robin estimate.

**Theorem 1.2 (Finite-family upper envelope).**

$$\operatorname{Esimp}\left(omega, coefficient, horizon\right) \leq horizon^{2} \times coefficientEnergy$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_ordered_simplex_energy_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite family has the horizon-squared upper envelope.

**Theorem 1.3 (Positive common-window constant).**

$$2 / delta < horizon\Rightarrow 0 < horizon^{2} - 4 / delta^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.ordered_simplex_coercivity_constant_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A horizon beyond the worst half-turn scale makes the lower constant strictly positive.

**Theorem 1.4 (Complex-coefficient lower coercivity).**

$$0 < delta \land \operatorname{gapFloor}\left(delta, omega\right) \Rightarrow (horizon^{2} - \frac4 / delta^{2}) \times \operatorname{sumNormSq}\left(coefficient\right) \leq \operatorname{EcomplexSimp}\left(omega, coefficient, horizon\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite lower bound applies to complex Fourier coefficients, with squared modulus as the coefficient energy.

**Theorem 1.5 (Complex-coefficient upper envelope).**

$$\operatorname{EcomplexSimp}\left(omega, coefficient, horizon\right) \leq horizon^{2} \times \operatorname{sumNormSq}\left(coefficient\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The horizon-squared upper envelope is unchanged for complex coefficients.

**Theorem 1.6 (Phase invariance).**

$$\operatorname{unitPhase}\left(phase\right) \Rightarrow \operatorname{EcomplexSimp}\left(omega, phase . coefficient, horizon\right) = \operatorname{EcomplexSimp}\left(omega, coefficient, horizon\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_phase_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent unit-modulus phases on the finite channels do not change the ordered-simplex energy. This channelwise norm identity does not supply the missing infinite-family Weil or Robin transport.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_lower_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_phase_invariant`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_complex_ordered_simplex_energy_upper_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_ordered_simplex_energy_lower_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.finite_ordered_simplex_energy_upper_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.ordered_simplex_coercivity_constant_pos`
- Dependency: [D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage](OrderedTimeSimplexSecondMagnusAverage.md)
