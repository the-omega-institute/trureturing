# A Lorentz integral bound from centered interval mass

## Abstract

Centered interval bounds control Lorentz-weighted mass.

**Theorem 1.1 (Integrating the centered interval bound).**

Lean statement: `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_mass_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_mass_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K(x) = 4/(4+x²) be integrable against a positive measure. If the mass of [-r,r] is at most 2ρr+B for every r ≥ 0, then the integral of K is at most 2πρ+B.

For 0 < u ≤ 1, the superlevel set of K at u is the closed interval of radius 2√(1/u−1). Its mass is bounded by ρ times its Lebesgue length plus B. Integrating in u gives the result, since K has Lebesgue integral 2π and the levels lie in an interval of length one.

**Theorem 1.2 (The bound for weighted finite configurations).**

Lean statement: `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_sum_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_sum_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put a Dirac mass of size w_j ≥ 0 at each location x_j in a finite family. The mass bound includes both endpoints. The integral becomes the sum of w_j K(x_j), and repeated locations contribute with their full weights.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_mass_upper`
- Truth anchor: `D5/S3/Fourier/Concentration/LorentzIntervalMass.lorentz_sum_upper`
