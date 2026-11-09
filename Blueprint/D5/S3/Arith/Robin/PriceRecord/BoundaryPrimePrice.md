# Boundary-one price loss

## Abstract

Boundary-one prime price loss and exact integer rounding.

All scalar parameters are real. Assume p>1, lambda>0 and t>=1. Set f_p(t)=log((1-p^(-t-1))/(1-p^-1)), F_p(t)=f_p(t)-lambda*t*log p, C=1+lambda^-1, c=log C/log p-1 and b=max(1,c). The domain is fixed at exponent at least one. Bernoulli KL is the existing D5/S0/Diagonal/MarginBound.bernoulliKL, with its existing nonnegativity theorem; it is not redefined here.

**Theorem 1.1 (Euler probabilities lie in the open unit interval).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.probability_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.probability_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p>1 and t>=1, 0<p^(-t-1)<1. This pays the logarithm and KL domain conditions in the subsequent proofs.

**Theorem 1.2 (Separate the two Euler logarithms).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.benefit_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.benefit_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same conditions, f_p(t)=log(1-p^(-t-1))-log(1-p^-1), with both positive logarithm arguments established.

**Theorem 1.3 (The real maximum on the boundary-one domain).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.boundary_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.boundary_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t>=1, F_p(t)<=F_p(b). The proof consumes ContinuousPrimeMaximum.continuous_prime_hasDerivAt and continuous_prime_slope_strictAntiOn, establishes the shifted critical point and its boundary slope, and derives increase before b and decrease after b. The existing exponent-zero maximum is not substituted for this domain.

**Theorem 1.4 (Two candidates dominate every integer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_candidates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_candidates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer k>=1 satisfies F_p(k)<=max(F_p(floor b),F_p(ceil b)). Both candidates are admissible. Monotonicity on either side of b proves the exhaustive comparison, including integral b and ties.

**Theorem 1.5 (A nonnegative loss for every integer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write J_p(t)=F_p(b)-F_p(t) and d_p=min(J_p(floor b),J_p(ceil b)). For every integer k>=1, 0<=d_p<=J_p(k). No optimality of k is assumed.

**Theorem 1.6 (The finite loss is the exact integer price gap).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One admissible integer k attains d_p=J_p(k) and dominates F_p(j) for every integer j>=1. Choosing either smaller candidate loss remains valid at a tie. This result is consumed by the full-vector lower bound.

**Theorem 1.7 (KL difference with the real reference retained).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.price_difference_kl`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.price_difference_kl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real x,t>=1 and every real lambda, put v=p^(-x-1), u=p^(-t-1). Then F_p(x)-F_p(t)=D_Ber(v||u)/(1-v)+(lambda-1/(p^(x+1)-1))*(t-x)*log p. The log-ratio and odds identities are proved, so the linear boundary term is not dropped.

**Theorem 1.8 (The active KL and logarithmic formulas).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If p^2<C, then c>1 and for every real t>=1, J_p(t)=D_Ber(C^-1||p^(-t-1))/(1-C^-1)=log((1-C^-1)/(1-p^(-t-1)))-lambda*log(C/p^(t+1)). The Bernoulli orientation and denominator are literal.

**Theorem 1.9 (The inactive boundary KL and excess price).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.inactive_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.inactive_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If C<=p^2, then b=1, d_p=0, lambda-1/(p^2-1)>=0 and J_p(t)=D_Ber(p^-2||p^(-t-1))/(1-p^-2)+(lambda-1/(p^2-1))*(t-1)*log p for every t>=1. The scaled KL is nonnegative by the canonical Bernoulli theorem. Equality C=p^2 is included and then the excess-price coefficient vanishes.

**Theorem 1.10 (The explicit active two-KL minimum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_integer_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_integer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p^2<C, d_p is exactly the minimum of D_Ber(C^-1||p^(-k-1))/(1-C^-1) at k=floor c and k=ceil c. The scalar formulas and two-candidate comparison are inputs to OwnClockRobinGap.original_margin_own_clock_gap. The derivation is repository mathematics informed by the supplied terminal paper and independent mathematical review; the paper and its review provide mathematical context rather than formal verification. No classical constant, six-band estimate or RH assertion is claimed here.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_integer_gap`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.active_loss`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.benefit_log`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.boundary_maximum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.inactive_loss`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_candidates`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_attained`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.integer_gap_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.price_difference_kl`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.probability_mem`
- Dependency: [D5/S0/Diagonal/MarginBound](../../../../S0/Diagonal/MarginBound.md)
- Dependency: [D5/S3/Arith/GoldenResource/ContinuousPrimeMaximum](../../GoldenResource/ContinuousPrimeMaximum.md)
