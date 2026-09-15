# Noisy Moment Atom Extremum

## Abstract

A positivity-preserving perturbation of Lagrange weights attains the exact finite noisy exterior-atom optimum.

**Definition 1.1 (Actual feasible probability weights).**

Lean statement: `D5/S3/Analytic/NoisyMomentAtomExtremum.momentAtomSet`

*Formalization.* `D5/S3/Analytic/NoisyMomentAtomExtremum.momentAtomSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two nonnegative normalized weight vectors, one with an additional atom at y, have coordinatewise-close raw moments through degree card(iota)-1. Zeroth-moment equality follows from the two exact normalizations.

**Theorem 1.2 (Constructive attained optimum).**

Lean statement: `D5/S3/Analytic/NoisyMomentAtomExtremum.finite_noisy_exterior_atom_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NoisyMomentAtomExtremum.finite_noisy_exterior_atom_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary distinct real nodes and an off-node point y, form Lagrange extrapolation coefficients c, their positive-sign 0/1 interpolant p, P=p(y), and the nonconstant coefficient cost L. A computed positive noise radius preserves the signs of c after a worst-direction moment perturbation. The proof constructs both probability vectors, verifies their normalization and saturated moment errors, and proves that the maximum atom at y equals (1+epsilon L)/P. The IsGreatest upper bound ranges over all feasible probability pairs on the specified supports.

## References

- Truth anchor: `D5/S3/Analytic/NoisyMomentAtomExtremum.finite_noisy_exterior_atom_sharp`
- Truth anchor: `D5/S3/Analytic/NoisyMomentAtomExtremum.momentAtomSet`
