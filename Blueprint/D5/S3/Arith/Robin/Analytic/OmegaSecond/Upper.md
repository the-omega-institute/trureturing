# Second-threshold Rankin upper estimate

## Abstract

The Rankin reduction and the optimized prime budget for the second distinct-prime threshold.

**Definition 1.1 (Second-threshold counting scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale is log(x)/(log(log(x))*sqrt(log(log(x)))), equal to log(x)/(log(log(x)))^(3/2) for sufficiently large x.

**Definition 1.2 (Explicit saddle parameter).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the prime cutoff P, the saddle parameter is pi*sqrt(log(P))/(2*sqrt(3)). It grows with the cutoff.

**Definition 1.3 (Fixed inverse Euler cost).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.eulerCost`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.eulerCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed cost is the logarithm of one plus the sum over natural n of n^(-2). It bounds the unweighted inverse Euler factors for every Rankin parameter at least two.

**Theorem 1.4 (Exact second-threshold Rankin reduction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.rankin_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.rankin_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x greater than exp(1) and every real s at least two, tailCount(1,x) is at most exp(s*budget(log(x))+remainder(log(x),s,x)+eulerCost). The finite count includes precisely the integers 1<=n<=x whose number of distinct prime divisors strictly exceeds log(x)/log(log(x))+log(x)/(log(log(x)))^2.

The prime cutoff is exactly log(x). The finite Euler product, localized weight decomposition and threshold cancellation retain the same integer count and real endpoint throughout.

**Theorem 1.5 (Divergence of the finer scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale_top`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-threshold scale tends to positive infinity as x tends to positive infinity. A fixed additive Euler cost therefore vanishes after division by this scale.

**Theorem 1.6 (Budget contribution at the saddle).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle_budget_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle_budget_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product saddle(P)*budget(P), divided by P/(log(P)*sqrt(log(P))), tends to pi/sqrt(3). The coefficient two in the exact prime budget combines with the explicit saddle constant.

This stage concerns an upper bound at the second distinct-prime threshold. A matching lower bound has not been established.

**Theorem 1.7 (Sharp second-threshold upper coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon>0, all sufficiently large real x satisfy tailCount(1,x)<=exp((2*pi/sqrt(3)+epsilon)*log(x)/(log(log(x)))^(3/2)). The strict second threshold and the range 1<=n<=x are exactly those of tailCount(1,x).

At the explicit saddle, the prime budget has limiting coefficient pi/sqrt(3), and the localized remainder has upper coefficient pi/sqrt(3) on the finer scale. The fixed Euler cost vanishes there. This is an upper bound only; a matching lower bound remains unproved.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.eulerCost`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.rankin_reduction`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.result`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle_budget_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale_top`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate](MovingEstimate.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight](MovingWeight.md)
