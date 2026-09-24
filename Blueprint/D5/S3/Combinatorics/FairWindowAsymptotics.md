# Asymptotics of the Optimal Fair-Window Defect

## Abstract

The optimal fair-source defect has leading coefficient one and a logarithmic second-order bound.

**Theorem 1.1 (Reciprocal leading term and normalized limit).**

Lean statement: `D5/S3/Combinatorics/FairWindowAsymptotics.fair_window_defect_asymptotics`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FairWindowAsymptotics.fair_window_defect_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d(R) be optimalFairDefect(R), the minimum of the exact independent fair-source defect over all deterministic binary R-window tables, cast from the rationals to the reals. As R tends to infinity through the natural numbers, d(R)-1/R is O(log(R)/R^2), and R*d(R) converges to one. Both conclusions concern this same source and this same minimum. Choose m = 4*(floor(log base two of R+1)+1). Then 2^m is at least (R+1)^4, m is O(log R), and eventually m lies between one and R/2. The finite upper bound gives d(R)-1/R at most (2m+1)/R^2. The lower bound 1/(R+2) gives d(R)-1/R at least -2/R^2. These bounds yield the stated error order. Finally log(R)/R tends to zero, so multiplying the error by R gives the normalized limit.

## References

- Truth anchor: `D5/S3/Combinatorics/FairWindowAsymptotics.fair_window_defect_asymptotics`
- Dependency: [D5/S3/Combinatorics/FairWindowDefect](FairWindowDefect.md)
- Dependency: [D5/S3/Combinatorics/FairWindowUpperBound](FairWindowUpperBound.md)
