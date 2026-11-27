# Exponential energy of a tent profile

## Abstract

An exponential weight gives an attained minimum and a cubic lower bound for a nonnegative peak.

Use the weight exp(-2|x|) on the real line. A nonnegative profile f with central value a >= 0 is constrained by f(x) >= a - L|x|, where L > 0. Its energy is the integral of the weight times f(x)^2.

**Theorem 1.1 (Attained minimum for a peak).**

Lean statement: `D5/S3/Fourier/Concentration/ExponentialTentEnergy.sharp_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ExponentialTentEnergy.sharp_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r = a/L. Among profiles satisfying the stated constraints with integrable energy density, the minimum is L^2 (r^2 - r + (1 - exp(-2r))/2). The tent max(a - L|x|, 0) is pointwise minimal and attains the integral. Its energy reduces by evenness to twice the integral over [0,r], which is evaluated with an explicit antiderivative.

**Theorem 1.2 (Cubic control of the peak).**

Lean statement: `D5/S3/Fourier/Concentration/ExponentialTentEnergy.cube_le_exponential_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ExponentialTentEnergy.cube_le_exponential_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same pointwise and integrability conditions, a^3 is at most (3/2) exp(2a/L) L times the energy. On the support of the tent, the exponential is bounded below by exp(-2r). Integrating the square of the tent on that interval gives the cubic term.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ExponentialTentEnergy.cube_le_exponential_energy`
- Truth anchor: `D5/S3/Fourier/Concentration/ExponentialTentEnergy.sharp_energy_bound`
