# Frequency separation for the two clocks

## Abstract

Independent conjugations and an integer field norm bound the Fourier frequencies of the two clocks.

**Definition 1.1 (The frequency of an integer mode).**

Lean statement: `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.clockFrequency`

*Formalization.* `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.clockFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With θ(d) = arccos(1 − d/1734), the mode (m,n) has frequency m(θ(724) − θ(244)) + n(θ(804) − θ(244)).

**Theorem 1.2 (Explicit separation from zero).**

Lean statement: `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.frequency_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.frequency_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integers m and n with at least one nonzero, put M = max(|m|,|n|). The absolute frequency times 128·1734^(32M) is at least one.

The three phases are (1734 − d + i√(d(3468 − d)))/1734. They lie in the compositum of three quadratic extensions, whose degree is at most eight. At the primes 41, 11 and 79 the Jacobi signs are negative on the diagonal and positive off it, in the order d = 244, 724, 804. The associated Frobenius automorphisms invert one phase at a time. Each phase has a nonintegral rational trace, which rules out finite order.

A relation among the three phases with exponents −m−n, m and n would, after independently inverting the phase with a nonzero coefficient, force a nontrivial power of that phase to equal one. Thus the signed product differs from one. Multiplying any phase or inverse by 1734 makes it integral. The degree bound and the sum of absolute exponents, at most 4M, then give the stated constant via the signed-product separation theorem and the inequality |exp(iu) − 1| ≤ |u| for real u.

This arithmetic bound applies to every nonzero integer mode. Estimating its sample average along Riemann zero ordinates requires a separate analytic estimate.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.clockFrequency`
- Truth anchor: `D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation.frequency_separation`
- Dependency: [D5/S3/Factorization/Galois/SquareRootArithmetic](../../Factorization/Galois/SquareRootArithmetic.md)
- Dependency: [D5/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation](AlgebraicPhaseSeparation.md)
