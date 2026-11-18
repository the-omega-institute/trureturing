# Exact second-threshold logarithmic limit

## Abstract

The exact logarithmic counting limit at the second distinct-prime threshold.

For N₂(x)=tailCount(1,x), the quotient log(N₂(x))/(log(x)/(log(log(x)))^(3/2)) tends to 2*pi/sqrt(3). The original strict second threshold and the integer range 1<=n<=x are retained. The lower bound uses one finite logistic grid for each requested accuracy, fixed independently of x; the upper bound uses the existing Rankin reduction.

The equal-number exchange construction on both sides of a primorial and the partition-constant mechanism have precedent in Erdős–Nicolas 1981, Section 1. The real center P=log(x) is corrected by a remote deletion set. This is an application and refinement of that method, with no claim that the exchange method originates in this repository.

**Theorem 1.1 (Maximum-term entropy bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_choose_ge_binEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_choose_ge_binEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural a at most m, log choose(m,a) is at least m*binEntropy(a/m)-log(m+1), including the endpoint cases. At p=a/m the binomial probabilities increase up to a and decrease after a, as their adjacent-term recurrence shows. Their sum is one, so the a-th term is at least 1/(m+1). Taking logarithms yields the bound. This is the finite maximum-term argument, with no Stirling estimate or asymptotic hypothesis. In the second-threshold construction it estimates the number of choices in each prime box; feasibility is proved separately by the exchange budget. The equal-number exchange method around a primorial and its partition-constant mechanism have precedent in Erdős–Nicolas 1981, Section 1.

**Definition 1.2 (Finite entropy estimate).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyLower`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

entropyLower(m,a) is m*binEntropy(a/m)-log(m+1), the lower estimate supplied by the maximum-term theorem.

**Theorem 1.3 (Entropy on a growing common scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy_lower_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy_lower_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any filter, suppose W tends to infinity, n/W tends to d>0, and k/W tends to d*q. Then entropyLower(n,k)/W tends to d*binEntropy(q). Continuity of binary entropy controls the first term; log(n+1)/(n+1) tends to zero and (n+1)/W tends to d, so the explicit finite loss disappears.

**Definition 1.4 (Correction majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correctionMajorant`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correctionMajorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The majorant is pi^2/(6*(1-pi^2/(6*s^2))). Its denominator is positive for s at least pi.

**Theorem 1.5 (Cubic sine bound for the correction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.kernel_correction_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.kernel_correction_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s at least pi, s*(pi/sin(pi/s)-s) is nonnegative and at most the correction majorant. The cubic lower bound for sine preserves the coefficient one sixth.

**Theorem 1.6 (Explicit limiting majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correction_majorant_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correction_majorant_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction majorant tends to pi^2/6 as s tends to positive infinity. This coefficient controls the localized prime-weight upper estimate.

**Theorem 1.7 (Finite inverse-power tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.finite_power_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.finite_power_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s>1, every positive natural cutoff N, and every finite set S of natural numbers strictly larger than N, the sum of n^(-s) over S is at most N^(1-s)/(s-1). The bound compares the finite sum with the integral over all real t>N.

**Theorem 1.8 (Small-endpoint geometric tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.small_weight_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.small_weight_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>=2 and s>=0, summing log(1+exp(-s*abs(log(n/P)))) over any finite set of positive natural numbers n<=P/2 gives at most P*(1/2)^s. This bound also applies to any selected primes in that range.

**Theorem 1.9 (Large-endpoint geometric tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.large_weight_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.large_weight_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>=2 and s>=2, the same localized weight summed over any finite set of natural numbers strictly greater than 2P is at most 2P*(2/3)^s. The real-to-natural cutoff is retained explicitly before the inverse-power tail estimate.

**Theorem 1.10 (Decay at the square-root logarithmic saddle).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.geometric_sqrt_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.geometric_sqrt_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0 and 0<q<1, t*sqrt(t)*q^(c*sqrt(t)) tends to zero as t tends to positive infinity. Thus each geometric tail vanishes on the normalized second-threshold scale at its explicit saddle.

**Theorem 1.11 (Rounded occupancy on a common scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.floor_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.floor_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If W tends to infinity and M/W tends to d>0, then floor(q*M)/W tends to q*d for every fixed nonnegative q. The pinned floor-ratio limit is composed with M tending to infinity and multiplied by M/W.

**Theorem 1.12 (Common capacity on a common scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.min_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.min_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two natural capacities divided by a positive growing scale both tend to d, then their minimum divided by the scale also tends to d. This supplies the equal capacity used for the two sides of each prime-box exchange.

**Definition 1.13 (Explicit moving-weight majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The majorant retains the explicit central kernel correction, the central prime-density error and both geometric tails. Each term is explicit in the real cutoff P and saddle parameter s.

**Theorem 1.14 (Uniform finite remainder bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder_le_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder_le_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large P, every s>=pi with s>=2, and every real endpoint x, remainder(P,s,x)<=majorant(P,s). The bound is uniform in x because the omitted prime terms are nonnegative.

**Theorem 1.15 (Explicit normalized majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0, majorant(P,c*sqrt(log(P))) divided by P/(log(P)*sqrt(log(P))) tends to pi^2/(6c) as P tends to positive infinity.

**Theorem 1.16 (Moving prime-weight upper coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.moving_weight_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.moving_weight_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0 and epsilon>0, all sufficiently large P satisfy, simultaneously for every real x, remainder(P,c*sqrt(log(P)),x)<=(pi^2/(6c)+epsilon)*P/(log(P)*sqrt(log(P))). This stage proves the explicit upper coefficient used in the counting estimate.

**Definition 1.17 (reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.reserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.reserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prime reserve (P/2,3P/4] is separated from every fixed active logarithmic box eventually.

**Definition 1.18 (boxScale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.boxScale`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.boxScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The capacity scale is P/(log(P)*c*sqrt(log(P))).

**Definition 1.19 (negativeBox).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.negativeBox`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.negativeBox` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The removable half-open prime box uses endpoints P*exp(-node(i+1)/s) and P*exp(-node(i)/s).

**Definition 1.20 (positiveBox).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.positiveBox`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.positiveBox` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The insertable half-open prime box uses endpoints P*exp(node(i)/s) and P*exp(node(i+1)/s).

**Definition 1.21 (capacity).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.capacity`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.capacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common capacity is the minimum of the two actual prime-box cardinalities.

**Definition 1.22 (occupancy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.occupancy`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.occupancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same integer floor(logistic(node(i+1))*capacity) is selected on both sides.

**Definition 1.23 (exchangeCost).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchangeCost`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchangeCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform worst-endpoint cost is (2/s)*sum(node(i+1)*occupancy(i)).

**Definition 1.24 (entropyEstimate).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyEstimate`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyEstimate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite entropy estimate is twice the sum of M*binEntropy(h/M)-log(M+1).

**Definition 1.25 (Strict integer threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer floor(P/log(P)+P/log(P)^2)+1 is strictly above the literal second threshold at x=exp(P).

**Definition 1.26 (Remote deletion size).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The excess is primeCounting(floor(P))-thresholdK(P), using natural subtraction.

**Definition 1.27 (Remote deletion budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guaranteed logarithmic slack is P-theta(P)+excess(P)*log(P/2). It does not assume theta(P)<P.

**Theorem 1.28 (Enough primes for the strict threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK_le_primeCount`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK_le_primeCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eventually thresholdK(P) is at most primeCounting(floor(P)), so the natural subtraction defining excess is exact.

**Theorem 1.29 (Asymptotic deletion size).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The excess divided by P/log(P)^3 tends to two. The floor error is negligible on this scale.

**Theorem 1.30 (Asymptotic usable budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deterministic coreBudget divided by P/log(P)^2 tends to two. Remote deletion removes only primes in (P/2,3P/4].

**Theorem 1.31 (A fixed grid with feasible cost and full entropy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fixed_grid_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fixed_grid_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive epsilon there are a positive saddle coefficient c and one finite grid independent of P. Eventually the total worst-endpoint exchange cost is at most coreBudget(P), and the logarithm of the product of squared binomial choices is at least (2*pi/sqrt(3)-epsilon)*P/(log(P)*sqrt(log(P))). The finite maximum-term entropy bound is used before taking these limits.

**Theorem 1.32 (Second-threshold logarithmic lower bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon, eventually log(tailCount(1,x)) is at least (2*pi/sqrt(3)-epsilon)*log(x)/(log(log(x)))^(3/2). All products counted are positive integers at most x with strictly more than the second threshold of distinct prime factors.

**Theorem 1.33 (Exact second-threshold logarithmic limit).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient log(tailCount(1,x))/(log(x)/(log(log(x)))^(3/2)) tends to 2*pi/sqrt(3). The construction uses equal-cardinality exchanges on both sides of a primorial cutoff and the partition-constant mechanism of Erdős–Nicolas 1981, Section 1; this method is not claimed as original to this repository. The real center P=log(x) uses a separate remote deletion to attain the exact threshold cardinality.

**Definition 1.34 (Second-threshold counting scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale is log(x)/(log(log(x))*sqrt(log(log(x)))), equal to log(x)/(log(log(x)))^(3/2) for sufficiently large x.

**Definition 1.35 (Explicit saddle parameter).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the prime cutoff P, the saddle parameter is pi*sqrt(log(P))/(2*sqrt(3)). It grows with the cutoff.

**Definition 1.36 (Fixed inverse Euler cost).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.eulerCost`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.eulerCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed cost is the logarithm of one plus the sum over natural n of n^(-2). It bounds the unweighted inverse Euler factors for every Rankin parameter at least two.

**Theorem 1.37 (Exact second-threshold Rankin reduction).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rankin_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rankin_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x greater than exp(1) and every real s at least two, tailCount(1,x) is at most exp(s*budget(log(x))+remainder(log(x),s,x)+eulerCost). The finite count includes precisely the integers 1<=n<=x whose number of distinct prime divisors strictly exceeds log(x)/log(log(x))+log(x)/(log(log(x)))^2.

The prime cutoff is exactly log(x). The finite Euler product, localized weight decomposition and threshold cancellation retain the same integer count and real endpoint throughout.

**Theorem 1.38 (Divergence of the finer scale).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale_top`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-threshold scale tends to positive infinity as x tends to positive infinity. A fixed additive Euler cost therefore vanishes after division by this scale.

**Theorem 1.39 (Budget contribution at the saddle).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle_budget_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle_budget_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product saddle(P)*budget(P), divided by P/(log(P)*sqrt(log(P))), tends to pi/sqrt(3). The coefficient two in the exact prime budget combines with the explicit saddle constant.

**Theorem 1.40 (Explicit second-threshold upper coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon>0, all sufficiently large real x satisfy tailCount(1,x)<=exp((2*pi/sqrt(3)+epsilon)*log(x)/(log(log(x)))^(3/2)). The strict second threshold and the range 1<=n<=x are exactly those of tailCount(1,x).

At the explicit saddle, the prime budget has limiting coefficient pi/sqrt(3), and the localized remainder has upper coefficient pi/sqrt(3) on the finer scale. The fixed Euler cost vanishes there.

**Definition 1.41 (Prime base and disjoint exchange bins).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.ExchangeSystem`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.ExchangeSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The system records the actual finite prime sets, their containment and separation properties.

**Definition 1.42 (Logarithmic boxes over a trimmed core).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmicExchangeSystem`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmicExchangeSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For monotone nodes starting at zero, the literal half-open boxes (P exp(-t_i/s),P exp(-t_(i-1)/s)] and (P exp(t_(i-1)/s),P exp(t_i/s)] give an exchange system. A reserve removed from (P/2,3P/4] misses every negative box when the lowest active endpoint is at least 3P/4. All disjointness and containment properties are proved, including floor endpoints.

**Definition 1.43 (Independent equal-size choices).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Choices`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Choices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every bin choose an h_i-element negative subset and an h_i-element positive subset. Choices is the product of these two finite dependent function types.

**Definition 1.44 (Removed union).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.removed`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.removed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the chosen negative subsets.

**Definition 1.45 (Inserted union).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.inserted`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.inserted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the chosen positive subsets.

**Definition 1.46 (Exchanged prime support).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.support`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove the negative union from the base and unite the result with the positive union.

**Definition 1.47 (Exchanged integer).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.value`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer value is the product of all primes in the exchanged support.

**Theorem 1.48 (Every choice is recoverable).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchange_value_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchange_value_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unique prime factorization recovers the exchanged support. Membership inside the base recovers the removed union; membership outside recovers the inserted union. Intersecting these unions with their disjoint bins recovers each individual choice, proving injectivity.

**Theorem 1.49 (The distinct-prime count is preserved).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.omega_exchange_value`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.omega_exchange_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal numbers of removed and inserted primes make omega of every exchanged product exactly the cardinality of the base.

**Theorem 1.50 (Exact independent-choice count).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.card_exchange_choices`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.card_exchange_choices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite choice type has cardinality the product over bins of choose(card(negative bin),h) times choose(card(positive bin),h). An overfull request has zero choices.

**Theorem 1.51 (Worst-endpoint logarithmic cost).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_exchange_value_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_exchange_value_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the base costs at most P-D, each removed prime costs at least log(P)-t_i/s, and each inserted prime at most log(P)+t_i/s, then every exchanged product has logarithm at most P-D+(2/s) sum_i t_i h_i. The factor two accounts for both endpoints of every pair.

**Theorem 1.52 (A feasible family in the strict tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.balanced_exchange_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.balanced_exchange_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the exchange cost is at most D, P is at most log(x), x is positive, and the base cardinality strictly exceeds the original threshold, the product of binomial choice counts is a lower bound for the original tailCount(lambda,x). This is a deterministic budget for every choice, with the strict threshold unchanged.

**Theorem 1.53 (Literal boxes fit the exchange budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmic_exchange_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmic_exchange_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic box endpoints supply the two cost inequalities directly. Consequently the exact product of their binomial choice counts is bounded by tailCount whenever the trimmed core, strict threshold, and finite exchange budget satisfy the stated conditions.

**Definition 1.54 (Three-term counting polynomial).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.countingThreeTerms`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.countingThreeTerms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is P/log(P)+P/log(P)^2+2P/log(P)^3. The prime count uses the natural floor of the real endpoint P.

**Theorem 1.55 (Three-term prime-counting expansion).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_three_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_three_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After subtracting the three-term polynomial, division by P/log(P)^4 gives limit six as P tends to positive infinity. This follows from the existing four-term expansion with its next residual coefficient twenty-four.

**Theorem 1.56 (Uniform eventual counting error).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all sufficiently large real P, the absolute difference between the prime count and P/log(P) is at most 3P/log(P)^2. The same bound applies at every endpoint beyond a single fixed threshold.

**Definition 1.57 (Second-threshold budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The budget is P-theta(P)+(primeCount(P)-P/log(P)-P/log(P)^2)*log(P). It retains the exact prime-counting and Chebyshev terms before normalization.

**Theorem 1.58 (Exact cancellation and residual coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The budget divided by P/log(P)^2 tends to two. The first two prime-counting terms cancel the threshold exactly; the third coefficient supplies two, while the Chebyshev error vanishes on this scale.

These estimates support an upper bound for integers whose number of distinct prime factors exceeds the second threshold.

**Theorem 1.59 (Uniform central prime-counting error).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_counting_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_counting_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large real P and every real t in the closed interval [P/2,2P], the absolute difference between primeCount(t) and t/log(P) is at most 28P/log(P)^2. The prime count includes primes at the floored real endpoint.

The constant density uses the same central endpoint P throughout the interval. The bound combines the uniform eventual error at t with the change from log(t) to log(P).

**Definition 1.60 (Localized weight).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight at P,s,t is log(1+exp(-s*abs(log(t/P)))).

**Definition 1.61 (Finite prime remainder).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remainder is the sum of the localized weight over all primes at most the natural floor of x.

**Theorem 1.62 (Nonnegative localized weight).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The localized weight is nonnegative for all real P,s,t.

**Theorem 1.63 (Continuity away from zero).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and a>0, the localized weight is continuous on every closed real interval [a,b], for every real s.

**Definition 1.64 (Smooth left extension).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left extension subtracts s*(log(P)-log(t)) from log(1+P^s/t^s).

**Theorem 1.65 (Left-branch identity).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_eq_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_eq_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0,t<=P, the smooth left extension equals the localized weight.

**Theorem 1.66 (Right-branch identity).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_eq_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_eq_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0,P<=t, log(1+P^s/t^s) equals the localized weight.

**Theorem 1.67 (Left-branch derivative).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0 and every real s, the left extension has derivative s/t-abelKernel(s,P^s,t).

**Theorem 1.68 (Left endpoint value at the peak).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and every real s, the smooth left extension at t=P equals log(2).

**Theorem 1.69 (Right endpoint value at the peak).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and every real s, log(1+P^s/P^s) equals log(2).

**Theorem 1.70 (Increasing left branch).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0, the left-branch derivative s/t-abelKernel(s,P^s,t) is nonnegative.

**Theorem 1.71 (Exact finite prime ramp decomposition).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_weight_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_weight_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,P<=x,s>=0, the sum over primes p<=x of log(1+P^s*p^(-s)) equals s*(primeCount(P)*log(P)-theta(P))+remainder(P,s,x). The natural-floor endpoints and the prime at the cutoff are retained exactly.

**Theorem 1.72 (Finite prime quadrature upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_quadrature_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_quadrature_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every real interval [a,b] with 0<=a<=b, let d be continuous and let f have derivative d throughout the interval. If abs(primeCount(t)-C*t)<=E there for E>=0, the prime sum of f over a<p<=b is at most C times the integral of f plus E*(abs(f(a))+abs(f(b))+the integral of abs(d)), with E multiplying the entire parenthesized expression. Both endpoints and the full variation are retained.

**Theorem 1.73 (Uniform moving-weight comparison).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_weight_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_weight_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large real P, the estimate holds for every s>=0: the localized prime-weight sum over P/2<p<=2P is at most its real integral over [P/2,2P] divided by log(P), plus 112*log(2)*P/log(P)^2.

The weight increases up to P and decreases after P, so its total variation is bounded independently of s. This prevents the error from growing with the moving saddle.

**Theorem 1.74 (Central continuum mass upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_integral_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_integral_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every P>0 and s>1, the integral over [P/2,2P] of log(1+exp(-s*abs(log(t/P)))) is at most P*(pi/sin(pi/s)-s)+(s/2+2)*P*2^(-s). The power-kernel integral is evaluated exactly before subtracting the linear ramp.

The remaining endpoint and removed-tail terms decay geometrically. The explicit upper majorant for the normalized kernel correction tends to pi^2/6.

The grid is fixed before the real cutoff varies. Its occupancy at distance u is q(u)=1/(1+exp(u)); H is Mathlib's binary entropy. The Mellin suppliers at exponents one and two give the integrals of q and u*q as log 2 and pi^2/12. Integration by parts then gives the integral of log(1+exp(-u)) as pi^2/12 and the integral of H(q(u)) as pi^2/6.

This is an analytic ingredient in equal-number exchanges around a primorial cutoff. The method precedent is Erdős–Nicolas 1981, Section 1, including exchanges on both sides of a primorial and the partition-constant mechanism. No claim of a new exchange method is made.

**Definition 1.75 (Occupancy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logistic`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logistic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(u)=(1+exp(u)) inverse.

**Definition 1.76 (Fermi logarithm).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fermiLog`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fermiLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J(u)=log(1+exp(-u)).

**Definition 1.77 (Logistic entropy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(q(u))=J(u)+u*q(u).

**Definition 1.78 (Uniform finite mesh).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Mesh`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Mesh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive endpoint U and positive natural number n specify a uniform partition of [0,U].

**Definition 1.79 (Mesh width).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The width delta=U/n.

**Definition 1.80 (Mesh nodes).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The i-th node is i*delta.

**Definition 1.81 (Endpoint cost).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.cost`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.cost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice the sum delta*t_i*q(t_i), over right endpoints.

**Definition 1.82 (Endpoint entropy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.mass`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice the sum delta*H(q(t_i)), over right endpoints.

**Theorem 1.83 (Positive mesh width).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every mesh has strictly positive width.

**Theorem 1.84 (Consecutive node difference).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every consecutive node difference equals the mesh width.

**Theorem 1.85 (Last grid node).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_end`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_end` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n-th node equals U.

**Theorem 1.86 (First grid node).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeroth node is zero.

**Theorem 1.87 (Explicit cost and entropy errors).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.grid_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.grid_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cost is at most pi^2/6+2*delta*log 2. The entropy is at least pi^2/3-2*(U+2)*exp(-U)-2*delta*log 2. Monotonicity of q controls cost without assuming monotonicity of u*q; entropy errors telescope along the partition.

**Theorem 1.88 (A fixed grid with prescribed slack).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exists_good_grid`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exists_good_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive eta and rho there is a finite grid with cost at most (pi^2/6)*(1+eta/2) and entropy at least pi^2/3-rho. Both U and n depend only on those tolerances, not on the real cutoff.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Choices`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.ExchangeSystem`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Mesh`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.balanced_exchange_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.boxScale`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.budget_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.capacity`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.card_exchange_choices`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_integral_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_counting_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.central_prime_weight_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.coreBudget_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correctionMajorant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.correction_majorant_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.cost`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.countingThreeTerms`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyEstimate`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyLower`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy_lower_scaled`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.eulerCost`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.excess_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchangeCost`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exchange_value_injective`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.exists_good_grid`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fermiLog`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.finite_power_tail`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.fixed_grid_exists`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.floor_scaled`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.geometric_sqrt_decay`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.grid_bounds`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.inserted`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.kernel_correction_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.large_weight_tail`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_at_cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_deriv_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.leftWeight_eq_weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_choose_ge_binEntropy`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_exchange_value_le`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmicExchangeSystem`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logarithmic_exchange_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.logistic`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.lower`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.majorant_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.mass`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.min_scaled`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.moving_weight_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.negativeBox`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_end`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_step`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.node_zero`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.occupancy`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.omega_exchange_value`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.positiveBox`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_error_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_counting_three_terms`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_quadrature_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.prime_weight_split`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rankin_reduction`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.remainder_le_majorant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.removed`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.reserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.result`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_at_cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.rightWeight_eq_weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.saddle_budget_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.secondScale_top`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.small_weight_tail`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.step_pos`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.support`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.thresholdK_le_primeCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.value`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_continuousOn`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.weight_nonneg`
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff](../ExceptionCount/PrimeCutoff.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Lower](../OmegaTail/Lower.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](../OmegaTail/Selection.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../../PriceRecord/QuantitativePrimeAbel.md)
- Dependency: [D5/S3/Weil/ZetaBridge/FermiMellin](../../../../Weil/ZetaBridge/FermiMellin.md)
