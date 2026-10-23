# The two moment inequalities

## Abstract

Successive moment minors for positive probability laws.

**Theorem 1.1 (Both inequalities).**

Lean statement: `D5/S3/Analytic/MomentMinors/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every interval I and every probability law on the positive reals satisfying the stated moment and logarithmic integrability conditions, both the eight-parameter inequality for phi and the displaced-parameter inequality for theta hold. All eight parameters of the first inequality belong to I. In the second inequality each of x,y,z,v and its displacement by a belongs to I.

The midpoint moment kernel is positive semidefinite. Taking its second minors on ordered parameter pairs gives a positive semidefinite kernel whose diagonal is xi and whose off-diagonal entries are the indicated differences of xi. The two central squared moment terms have the same argument and cancel. A further second-minor construction on four parameter pairs, followed by a two by two determinant, yields the eight-parameter inequality.

On pairs (x,x+a), the same second-minor kernel is sigma evaluated at the midpoint of the two base parameters. Its second minors have diagonal theta. Applying the same determinant argument and cancelling the two equal central sigma terms yields the displaced-parameter inequality. Repeated parameters, zero minors, and either sign of the displacement are included.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/Result.result`
- Dependency: [D5/S3/Analytic/MomentMinors/MomentKernel](MomentKernel.md)
- Dependency: [D5/S3/Analytic/MomentMinors/PairMinor](PairMinor.md)
