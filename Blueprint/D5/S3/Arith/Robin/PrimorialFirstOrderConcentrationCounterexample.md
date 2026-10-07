# First Order Bounds and Concentration at Zero

## Abstract

A smooth perturbation of the original Robin profile has vanishing first-order error and divergent exactly compensated integrals.

Let Phi(v) be the original literal profile integral from PrimorialGlobalLaplaceEnvelope, and let r(v) be its logarithmic derivative. For epsilon>0 take delta=exp(-1/epsilon^2), h(v)=epsilon*delta*(1-exp(-v/delta)), F(v)=Phi(v)*exp(h(v)), and S(v)=r(v)+epsilon*exp(-v/delta). The concentration width delta is chosen much smaller than the first-order error epsilon.

**Theorem 1.1 (First order control does not suffice for the compensated integral).**

Lean statement: `D5/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0, F(0)=1, F'=F*S, S(0)=1+epsilon, and S is strictly decreasing and positive on the nonnegative axis. On the entire axis v>=0, abs(S(v)-r(v))<=epsilon and exp(-epsilon*v)*Phi(v)<=F(v)<=exp(epsilon*v)*Phi(v).

The exact compensation keeps S(0). Its difference from the original compensated numerator is Delta(v)=Phi(v)*(exp(h(v))-1)-epsilon*v, with Delta(0)=Delta'(0)=0. For every fixed sigma>0, both full compensated integrals and their difference are absolutely integrable on (0,infinity). The difference equals the integral of exp(-sigma*v)*Delta(v)/v^2 and tends to minus infinity as epsilon tends to zero from the right.

The proof bounds the whole tail negatively and retains a negative logarithmic contribution between 8*exp(1)*delta and 1. The numerator is kept intact at zero. This constructed family is a counterexample to the sufficiency of first-order information. It is not the finite-prime Euler family and does not decide the actual Robin residual or RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimorialFirstOrderConcentrationCounterexample.result`
- Dependency: [D5/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope](PrimorialGlobalLaplaceEnvelope.md)
