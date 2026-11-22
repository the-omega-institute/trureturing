# Sparse ordinate mass

## Abstract

Dyadic transfer from sparse real cutoffs to harmonic mass.

**Theorem 1.1 (Sparse counts bound the weighted mass).**

Lean statement: `D5/S3/Analytic/Oscillation/SparseOrdinateMass.cutoffMass_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SparseOrdinateMass.cutoffMass_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let gamma be a real ordinate family with finite inclusive lower cutoffs. Let m and w be nonnegative weights, with w(j) at most m(j)/gamma(j) whenever gamma(j) is positive. If the cutoff sum B of m satisfies B(T)/(T log T) tending to zero, the cutoff sum W of w satisfies W(T)/(log T)^2 tending to zero. For positive T, the shell with T/2 < gamma <= T adds at most 2 B(T)/T. Above a fixed cutoff, successive halving bounds the shell contributions by an arbitrarily small multiple of (log T)^2, because each difference of squared logarithms dominates log(2) log(T). The fixed initial mass vanishes after normalization.

**Theorem 1.2 (Harmonic mass with natural multiplicities).**

Lean statement: `D5/S3/Analytic/Oscillation/SparseOrdinateMass.harmonicMass_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SparseOrdinateMass.harmonicMass_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive ordinates and natural multiplicities m(j), take the weight m(j) gamma(j)/(1/4 + gamma(j)^2). It is nonnegative and bounded by m(j)/gamma(j), so the same inclusive cutoff count controls its mass.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SparseOrdinateMass.cutoffMass_tendsto_zero`
- Truth anchor: `D5/S3/Analytic/Oscillation/SparseOrdinateMass.harmonicMass_tendsto_zero`
