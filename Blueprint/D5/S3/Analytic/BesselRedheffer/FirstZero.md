# The first positive zero

## Abstract

Positivity before the first zero and a radial trial-function estimate.

**Theorem 1.1 (Positivity before the first zero).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_pos_of_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_pos_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For order nu greater than -1 and 0 less than or equal to x less than the first positive zero, the normalized series is positive at x. If it were nonpositive, continuity and its value one at zero would produce a positive zero no greater than x, contradicting the defining infimum.

**Theorem 1.2 (The radial trial-function estimate).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu at least thirty, if the normalized series is positive on the closed interval from zero to a positive z, then z squared is at most (6/5)(nu+1)(nu+7). With y(r) equal to the series at zr, weight w(r)=r to the power 2nu+1, logarithmic derivative h=y prime/y, and trial function u(r)=(1-r squared) cubed, the weighted square of u prime minus hu integrates to the energy minus z squared times the weighted norm. The boundary term vanishes. Expanding the two polynomial factors and integrating powers gives the energy equal to (6/5)(nu+1)(nu+7) times the weighted norm. The norm is strictly positive.

**Theorem 1.3 (The infimum is positive).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu at least thirty, a positive zero exists: otherwise positivity would hold on arbitrarily long intervals, contradicting the energy estimate. The infimum is nonnegative and is itself a zero. Positivity at the origin excludes a zero infimum, so the first zero is strictly positive.

**Theorem 1.4 (The infimum is a zero).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_firstZero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_firstZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu at least thirty, the set of positive zeros is nonempty, bounded below and closed. It is closed because continuity makes the zero set closed and the value one at the origin excludes zero. The infimum therefore belongs to the set.

**Theorem 1.5 (An upper bound for the first zero).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real nu at least thirty, the first positive zero squared is at most (6/5)(nu+1)(nu+7). If it were larger, an argument strictly between the square root of this bound and the first zero would have positivity throughout its closed initial interval, contradicting the energy estimate.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_pos`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/FirstZero.firstZero_sq_le`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_energy_bound`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_firstZero`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/FirstZero.nbessel_pos_of_lt`
- Dependency: [D5/S3/Analytic/BesselRedheffer/Series](Series.md)
