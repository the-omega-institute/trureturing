# Compact normalized selection profiles

## Abstract

Compact restrictions of a selection density can be normalized without losing its limiting logarithmic moment or entropy.

**Theorem 1.1 (Compact profile approximation).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Truncation.compact_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Truncation.compact_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1 and every positive accuracy, there are positive endpoints A<B and a continuous function g on [A,B] taking values strictly between zero and one. Its integral on (A,B] is exactly one. Its logarithmic moment approximates log(a(s))-(pi/s)*cos(pi/s)/sin(pi/s), and its binary entropy integral exceeds s-pi*cos(pi/s)/sin(pi/s) minus the chosen accuracy.

Restrict q(s,u) to nested compact windows exhausting the positive half-line. Absolute integrability gives simultaneous convergence of mass, logarithmic moment and entropy. If M is the mass of a sufficiently large restriction, set g(u)=q(s,M*u) on the horizontally rescaled window. Scalar change of variables gives mass one, logarithmic moment -log(M) plus the truncated moment divided by M, and entropy equal to the truncated entropy divided by M. Since M tends to one, these quantities approach the stated limits.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Truncation.compact_profile`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Density](Density.md)
