# Counting positive ordinates

## Abstract

Weighted counts and triangular averages of a locally finite positive spectrum.

**Theorem 1.1 (An eventual logarithmic counting bound).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.count_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The counting asymptotic implies a positive constant B with N(M) at most B M log M for all sufficiently large M.

**Theorem 1.2 (Monotonicity of weighted counts).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.count_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.count_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplicity-weighted counting function of a positive locally finite spectrum is monotone in the real cutoff. Increasing the cutoff enlarges the finite sum of nonnegative multiplicities.

**Theorem 1.3 (Separation from zero).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.positive_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.positive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let gamma be a family of distinct positive real ordinates, with only finitely many ordinates below each real bound. There exists b>0 such that every ordinate is greater than b. A positive minimum for the finite set below one, together with the bound one for its complement, gives the gap.

**Theorem 1.4 (Inverse-square tails).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.inverse_square_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.inverse_square_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If N(T)/(T log T) tends to 1/(2 pi), there is a nonnegative constant C such that, for every T at least four, the sum of multiplicity divided by the square of the ordinate over all ordinates greater than T converges and is at most C log(T)/T. Monotonicity extends an eventual logarithmic counting bound to all cutoffs at least four. Integrating that bound controls every finite subset of the tail and hence the infinite sum.

**Theorem 1.5 (Triangular lower mass).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.lower_triangular_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.lower_triangular_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give each ordinate a positive integer multiplicity and write N(T) for the total multiplicity at ordinates at most T. If N(T)/(T log T) tends to 1/(2 pi), then the sum of multiplicities weighted by max(0,1-gamma/M), divided by M log M, tends to 1/(4 pi). The triangular sum is the integral of N(Mu) for 0<u<=1. After normalization, the integrand tends to u/(2 pi); monotonicity of N supplies a constant integrable bound.

**Theorem 1.6 (An upper band with substantial triangular mass).**

Lean statement: `D5/S3/Analytic/Oscillation/OrdinateCounting.select_upper_band`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/OrdinateCounting.select_upper_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume N(T)/(T log T) tends to 1/(2 pi). For every fixed b>0 there is a constant cb>0 such that, for all sufficiently large T, some U in [T,2T] has triangular mass Wplus(b,U) at least cb log T. The total multiplicity at ordinates with abs(gamma-U)<b is at most twelve times that triangular mass. One may take cb=b/(200 pi). Integrate the two finite sums over the centers in [T,2T]. Each counting window contributes at most 2b. The middle half of each triangle contributes at least b/2, and the ordinates between 17T/16 and 31T/16 supply enough total multiplicity. If every center failed one of the two inequalities, integration would contradict these bounds. No local counting estimate is assumed.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.count_mono`
- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.count_upper`
- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.inverse_square_tail`
- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.lower_triangular_mass`
- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.positive_gap`
- Truth anchor: `D5/S3/Analytic/Oscillation/OrdinateCounting.select_upper_band`
- Dependency: [D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness](../Asymptotics/LogarithmicPhaseStiffness.md)
- Dependency: [D5/S3/Analytic/Fourier/AngularFejerKernel](../Fourier/AngularFejerKernel.md)
