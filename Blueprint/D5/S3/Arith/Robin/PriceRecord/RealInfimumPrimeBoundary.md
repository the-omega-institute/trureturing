# Finite identities, full-image bounds and prefix scales

## Abstract

Exact finite prime-boundary formulas for the genuine real-infimum objective.

Exact finite identities and the full-image squeeze supply the original real second-order limit.

The imported definitions are unchanged frozen original objective definitions: S is a finite set of natural primes, admissible S a means a_p>=1, theta S=sum log p, clock S a=sum a_p log p, terminalCost T=log(log T), phi retains EulerGamma and the exact boundary-price benefit, realValues is its image on ALL admissible real functions, realInfimum=sInf(realValues), and baseline is EulerGamma+log(log(theta S))+sum log(1-p^-1). The new deficiency is only the finite abbreviation U(a)=-sum log(1-p^(-a_p-1)). No objective or baseline is redefined.

**Theorem 1.1 (Finite head and tail at any positive price).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.finite_boundary_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.finite_boundary_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C=cutoff(lambda)=1+lambda^-1>1 and A={p in S:p^2<=C}. For every prime p>1, log p>0. The logarithm comparison log(p^2)<=log C is equivalent to critical>=1; it yields b=critical in A, including equality. Its clock increment is log C-2 log p and its probability is C^-1 by the real-power exponential definition. In the complement b=1, its clock increment is zero and its probability is p^-2. Splitting the two finite sums proves Delta=card(A)*log C-2*theta(A) and U=card(A)*[-log(1-C^-1)]+sum_(S\A)[-log(1-p^-2)]. At p^2=C both probability expressions coincide and the clock increment vanishes.

**Theorem 1.2 (All finite prefix endpoints).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prime_prefix_boundary_formulas`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prime_prefix_boundary_formulas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For S=Nat.primesLE P and y=sqrt C, put x=min(P,y). A membership proof using Nat.le_floor_iff and Real.le_sqrt identifies A with Nat.primesLE floor(x). Its card is primeCounting floor(x), and its log sum is the literal Chebyshev theta x. The complementary set is exactly the prime-filtered natural Ioc floor(x) P. Therefore Delta=pi(x)*log C-2*theta(x) and U=pi(x)*[-log(1-C^-1)]+sum_(x<p<=P)[-log(1-p^-2)]. The formulas cover y>P, an empty head, prime lower ties, and the included upper endpoint.

**Theorem 1.3 (Exact cancellation against the Nicolas baseline).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.boundary_dual_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.boundary_dual_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the admissible boundary vector, benefit_log expresses each benefit as log(1-probability)-log(1-p^-1). Sum over the same finite support, substitute the literal phi and baseline definitions, and cancel. The resulting identity is phi(b)-baseline=F(T_b)-F(H)+U(b). Each logarithm has the domain furnished by p>1 and b>=1; no assumption on the sign of the global baseline is made.

**Theorem 1.4 (The finite dual quantity Q).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.fixed_price_Q_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.fixed_price_Q_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For prime S of card>=3, theta_gt_one gives H>1 and lambda=g(H)=1/(H log H)>0. Add the literal tangentRemainder(H,T_b)=F(H)+lambda*(T_b-H)-F(T_b) to the preceding identity. It gives exactly Q=U(b)+(T_b-H)/(H log H). No limiting property of Q is an input.

**Theorem 1.5 (Uniform finite bound on the actual sInf).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.real_infimum_fixed_price_squeeze`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.real_infimum_fixed_price_squeeze` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For card S>=3, ell=log H>=1 and any r>0, set A=exp(ell*(exp r-1))-1. The proof works pointwise on each original admissible real vector x. Put T=clock S x and u=(T-H)/H>=0. The exact benefit-log identity gives phi(x)-baseline=F(T)-F(H)+U(x), with U(x)>=0. The nested-log identity and two applications of the pinned elementary log bound give F(T)-F(H)>=u/ell-u^2/ell. Summing boundary_maximum and distributing the literal finite price objectives gives Q-u^2/ell<=phi(x)-baseline. If this gap is below r, invert both positive logarithms to obtain u<A; otherwise r already bounds it. Thus min(r,Q-A^2/ell) bounds every original value gap. Applying le_csInf to the same nonempty realValues proves the lower bound. The feasible boundary vector and real_infimum_bounds give realInfimum<=phi(b). Nonnegative tangentRemainder then gives realInfimum-baseline<=Q. All conditional-completeness premises come from the literal nonempty and bounded-below value set, with no attained optimizer, stationarity or RH premise.

**Definition 1.6 (deficiency).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.deficiency`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.deficiency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite logarithmic Euler deficit is minus the sum of log(1-probability(p,a(p))) on the original finite prime support.

**Definition 1.7 (prefixH).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prime-prefix clock H is the sum of log(p) over primes p at most P; it is the literal theta used by the original real-image objective.

**Definition 1.8 (prefixEll).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixEll`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixEll` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The secondary logarithmic scale ell is log(H), including all small prefixes as defined by the real logarithm.

**Definition 1.9 (prefixPrice).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixPrice`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixPrice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical price is the original g(H)=1/(H*log(H)); eventual positivity is proved rather than imposed on the final theorem.

**Definition 1.10 (prefixC).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixC`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed-price cutoff satisfies C=1+H*ell. Its additive one is retained through the second-order normalization.

**Definition 1.11 (prefixY).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixY`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The head-tail splitting point is Y=sqrt(C), with the actual finite upper endpoint P retained in the tail.

**Definition 1.12 (prefixBoundary).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixBoundary`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real boundary vector evaluates the existing pointwise price boundary at the canonical price, without asserting that it attains the original infimum.

**Definition 1.13 (prefixQ).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixQ`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is the boundary objective minus the original baseline, plus the exact nonlinear tangent remainder. Its finite formula joins the head and the finite Euler tail.

**Theorem 1.14 (prefix H ratio).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_H_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_H_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned theta prime-number theorem yields H/P tending to one for natural prime prefixes.

**Theorem 1.15 (prefixH atTop).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual clock H tends to infinity by multiplying H/P tending to one by the natural-cast sequence tending to infinity.

**Theorem 1.16 (prefix Y atTop).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual cutoff Y tends to infinity, using C=1+H*ell and the square root limit.

**Theorem 1.17 (prefix Y div cutoff).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint separation Y/P tends to zero. This proves that the finite prime tail has lower endpoint below its original upper endpoint eventually.

**Theorem 1.18 (eventual prefix domains).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_prefix_domains`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_prefix_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eventually the support is prime, has at least three members, ell is at least one, the price is positive, and 2<Y<P. These jointly pay the finite identities and full-image squeeze.

**Theorem 1.19 (eventual scale positivity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_scale_positivity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_scale_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual H, ell, C, Y, log(Y), P and log(P) are all positive eventually; every later denominator uses these paid domains.

**Theorem 1.20 (prefix C div H ell).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_C_div_H_ell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_C_div_H_ell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained cutoff correction C/(H*ell) tends to one because C=1+H*ell and H*ell tends to infinity.

**Theorem 1.21 (eventual log C identity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_log_C_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_log_C_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive eventual domain, log(C)=ell+log(ell)+log(C/(H*ell)); the exact correction is retained.

**Theorem 1.22 (prefix log Y div ell).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_log_Y_div_ell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_log_Y_div_ell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff logarithm obeys log(Y)/ell tending to one-half, using the exact logarithmic identity and the vanishing log(ell)/ell correction.

**Theorem 1.23 (prefix Y div sqrt H ell).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_sqrt_H_ell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_sqrt_H_ell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual square-root scale Y/sqrt(H*ell) tends to one; the additive cutoff correction is kept until taking the limit.

**Theorem 1.24 (exp difference quotient).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.exp_difference_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.exp_difference_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any filter and real argument u tending to zero and eventually nonzero, (exp(u)-1)/u tends to one. The punctured-neighborhood condition is explicit and is proved separately for both exponential remainders.

The consumed prefix domains, scales and exponential divided difference are consolidated with the finite squeeze in this owner. The argument asserts neither a sign for the Nicolas baseline nor integer Robin or RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.boundary_dual_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.deficiency`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_log_C_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_prefix_domains`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.eventual_scale_positivity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.exp_difference_quotient`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.finite_boundary_sums`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.fixed_price_Q_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixBoundary`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixC`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixEll`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixH_atTop`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixPrice`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixQ`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefixY`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_C_div_H_ell`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_H_ratio`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_atTop`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_cutoff`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_Y_div_sqrt_H_ell`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prefix_log_Y_div_ell`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.prime_prefix_boundary_formulas`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary.real_infimum_fixed_price_squeeze`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport](OwnClockFixedSupport.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
