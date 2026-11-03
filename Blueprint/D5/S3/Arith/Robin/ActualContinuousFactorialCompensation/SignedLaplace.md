# A negative signed Laplace average

## Abstract

A negative signed Laplace average of the actual factorial compensation.

G is the literal factorial compensation of Basic, with its complete von Mangoldt dilation sum, integral-defined alpha, and right-closed real-floor sums. The inherited arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. The exact G_formula is reused from Basic, arbitrary-rate exponential moment integrability is reused from PrimorialFirstOrderConcentrationCounterexample, and Gamma integral evaluation remains from pinned Mathlib; the Euler and logarithm brackets are reused from RobinRationalBasis. This is a repository deduction, with no literature novelty claim.

**Theorem 1.1 (The strict negative average).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SignedLaplace.G_signed_laplace_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SignedLaplace.G_signed_laplace_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Without additional hypotheses, f(t)=(1-10*t)*exp(-(21/2)*t)*G(exp(t)) is Lebesgue integrable on (0,infinity), and its integral is strictly less than -1/1000. This is a signed average, with no RH, zero-exclusion, or pointwise positivity conclusion.

Write F(d,y)=d*(y-1)-y*log(y). Finite smoothing on the literal floor cells gives G(x)=F(1+gamma-alpha,x) for 1<=x<2 and adds F(1+gamma+log(2),x/2) for 2<=x<3. The added term vanishes at x=2. The model is used outside this matching range only with the full actual-minus-model tail paid.

At the actual right-closed cutoff N=20, H(20)=55835135/15519504. J_tail_from_slope and T_epsilon_quadratic_bound give the alpha identity with error at most 1/25. Nineteen eight-term dyadic logarithm brackets, log(1)=0, and the existing gamma bracket prove 1479615/10000000<alpha<2279659/10000000 and gamma-alpha>3492496/10000000>17/50.

Positive-rate Gamma moments and translation of the half-line evaluate the two-cell signed integral. Its first-cell coefficient is -1604/159201; the shifted log(2) contribution is strictly negative. The model integral is less than -94846/75620475. No differentiation under an integral is used.

The global actual bound and the model bound prove absolute integrability. The discrepancy vanishes below log(3). Its full tail is bounded using the polynomials (13/5)*t+(53/2)*t^2+5*t^3 at rate 21/2 and 11/4+29*t+15*t^2 at rate 19/2. Translation and the binomial theorem give every tail moment. Only the polynomial argument is enlarged to 11/10; the exponential remains at log(3). The integer inequality 3^21>100000^2 gives exponential bounds 1/100000 and 3/100000. The two tails total at most 65567192153/277905245625000, leaving the integral below -282991857847/277905245625000<-1/1000.

The Reg mirror retains the exact source law and equivalence bridge. Whole-family variation, sensitivity, observational dependence and source selection remain unfinished; no validated four-slot registration is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SignedLaplace.G_signed_laplace_negative`
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Cancellation](SharpTail/Cancellation.md)
- Dependency: [D5/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample](../PrimorialFirstOrderConcentrationCounterexample.md)
