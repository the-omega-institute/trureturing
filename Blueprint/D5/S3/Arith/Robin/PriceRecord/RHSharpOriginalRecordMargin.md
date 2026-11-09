# The original integer, all positive predecessors, and sharp attainment

## Abstract

Sharp lower Robin-margin endpoint for original positive-price strict records

**Theorem 1.1 (The unconditional full correction at original records).**

$$\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; 2 \le T \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \Rightarrow \left(T \le \operatorname{largestPrime}\left(m\right) \Rightarrow \left(1 < \operatorname{theta}\left(\operatorname{largestPrime}\left(m\right)\right) \land \left(1 < \operatorname{log}\left(m\right) \land \left|\operatorname{D}\left(\operatorname{largestPrime}\left(m\right)\right) \cdot \operatorname{C}\left(m\right) - 2 \cdot \operatorname{sqrt}\left(2\right)\right| < epsilon\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.fullC_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C(m) denotes FullArithmeticCorrectionSecondOrder.correction(m). For every epsilon>0 one T>=2 works for all original positive-price strict records after the largest-prime cutoff, retaining both logarithmic domains.

**Definition 1.2 (The exact last prime of a real cutoff).**

$$\forall x \in \mathbb{R},\; \operatorname{Pn}\left(x\right) = \operatorname{FinsetSup}\left(\operatorname{primesLE}\left(\operatorname{floorNat}\left(x\right)\right), id\right)$$

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pn(x) is the natural Finset supremum, with the natural empty-set convention, of all primes at most floorNat(x).

**Theorem 1.3 (B depends only on this prime prefix).**

$$\forall x \in \mathbb{R},\; \operatorname{B}\left(\operatorname{Pn}\left(x\right)\right) = \operatorname{B}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.B_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact identity holds for every real x, with the existing totalized logarithms; no asymptotic replacement of Pn is made.

**Theorem 1.4 (Every real prime prefix has a genuine original record).**

$$\forall x \in \mathbb{R},\; 2 \le x \Rightarrow \left(\exists m \in \mathbb{N},\; \exists lambda \in \mathbb{R},\; 2 \le m \land \left(0 < lambda \land \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \land \left(\operatorname{primeFactors}\left(m\right) = \operatorname{primesLE}\left(\operatorname{floorNat}\left(x\right)\right) \land \operatorname{largestPrime}\left(m\right) = \operatorname{Pn}\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.cutoff_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least positive global optimizer pays strict dominance over every positive predecessor. Its primeFactors are exactly primesLE(floorNat(x)), and its largest prime is exactly Pn(x).

**Theorem 1.5 (The exact cutoff prime tends to infinity).**

$$\operatorname{Tendsto}\left(Pn, atTop, atTop\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural Pn is cast to Real for this limit.

**Theorem 1.6 (The true cutoff has asymptotically identical normalization).**

$$\lim_{x\to\infty}\frac{\operatorname{D}\left(\operatorname{Pn}\left(x\right)\right)}{\operatorname{D}\left(x\right)}=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D(x)=sqrt(x)*log(x); the limit is on the real atTop filter.

**Theorem 1.7 (The complete original margin splits exactly).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \Rightarrow \operatorname{robinLogMargin}\left(m\right) = \operatorname{B}\left(\operatorname{largestPrime}\left(m\right)\right) + \operatorname{C}\left(m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.margin_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction C is full; the original positive-price and all positive strict-predecessor hypotheses remain in the public identity.

**Definition 1.8 (The complete lower endpoint constant).**

$$K = 2 \cdot \operatorname{sqrt}\left(2\right) - 2 - firstLiMass$$

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete arithmetic correction contributes 2*sqrt(2), while the real B lower endpoint contributes -2-firstLiMass.

**Theorem 1.9 (Both sharp-endpoint quantifiers on genuine original records).**

$$\operatorname{RiemannHypothesis} \Rightarrow \left(\left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; 2 \le T \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \Rightarrow \left(T \le \operatorname{largestPrime}\left(m\right) \Rightarrow K - epsilon < \operatorname{D}\left(\operatorname{largestPrime}\left(m\right)\right) \cdot \operatorname{robinLogMargin}\left(m\right)\right)\right)\right)\right)\right)\right) \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\forall Y \in \mathbb{R},\; \exists m \in \mathbb{N},\; \exists lambda \in \mathbb{R},\; 2 \le m \land \left(0 < lambda \land \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(n < m \Rightarrow \operatorname{goldenResourceObjective}\left(lambda, n\right) < \operatorname{goldenResourceObjective}\left(lambda, m\right)\right)\right) \land \left(Y < \operatorname{largestPrime}\left(m\right) \land \left(1 < \operatorname{theta}\left(\operatorname{largestPrime}\left(m\right)\right) \land \left(1 < \operatorname{log}\left(m\right) \land \left|\operatorname{D}\left(\operatorname{largestPrime}\left(m\right)\right) \cdot \operatorname{robinLogMargin}\left(m\right) - K\right| < epsilon\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put M=firstLiMass, D(t)=sqrt(t)*log(t) and K=2*sqrt(2)-2-M. The objective is the canonical GoldenResourceOptimalInteger.goldenResourceObjective(lambda,n), defined as log(sum_(d in n.divisors)(d:Real)^(-1))-lambda*log(n). ObjectiveCore's golden_resource_sigma_identity identifies it with log(sigma_1(n)/n)-lambda*log(n). Neither objective nor robinLogMargin is redefined.

Under RH, for every epsilon>0 a SINGLE real T>=2 is chosen before m and lambda. Every original natural m>=2 and real lambda>0 with forall n:Nat, 0<n -> n<m -> objective(lambda,n)<objective(lambda,m), and P=largestPrime(m)>=T, satisfies D(P)*robinLogMargin(m)>K-epsilon. Also, for every epsilon>0 and every real Y, genuine m:Nat and lambda:Real exist with m>=2, lambda>0, that SAME FULL positive strict-predecessor condition, P>Y, theta(P)>1, log(m)>1 and abs(D(P)*robinLogMargin(m)-K)<epsilon. No all-integer RH statement, finite 5040 closure or opposite endpoint is asserted.

For each real x>=2 set N=floorNat(x), lambda=ActualBalancedCutoff.firstLayerPrice(N+1), and Pn(x)=sup id (Nat.primesLE N). The logarithms make lambda positive. firstLayerPrice_strictAnti and golden_layer_marginal_one_eq_log_one_add_inv give, for EVERY prime p, strict first-layer activation iff p<N+1 iff p<=N, including the excluded equality p=N+1. optimal_layer_count_spec supplies a positive minimal optimizer m whose factorizations are the strict counts and which divides every positive optimizer. At k=1, positive_layers_eq_count_interval and the prime factorization criterion identify m.primeFactors=primesLE N. Active prime 2 gives m>=2.

For ANY 0<n<m, global optimality gives objective(n)<=objective(m). If strictness failed, equality would make n another positive optimizer: every k>=1 has objective(k)<=objective(m)=objective(n). Minimality then gives m|n, whence m<=n, a contradiction. This pays the full positive predecessor telescope, including n=1 and n=2 when they are predecessors. Higher-layer ties stay excluded by strict counts. No uniqueness or noncritical-price premise is used.

Finset.sup_le gives Pn<=N and Finset.le_sup puts every prime p<=N below Pn. Therefore primesLE(Pn)=primesLE(N) without needing supremum membership first, and largestPrime(m)=Pn. theta_eq_sum_primesLE gives theta(Pn)=theta(x). The E₃ definition in Third has trailing +log(log(x))+gamma OUTSIDE its prime sum. Using primesLE_eq_filter_Ioc_zero gives E₃(Pn)-log(log(Pn))=E₃(x)-log(log(x)), and hence B(Pn)=B(x) exactly. E₃(Pn)=E₃(x) is not used.

For every real bound Y, Nat.exists_infinite_primes gives a fixed prime p>=ceilNat(Y). When x>=p, Nat.le_floor puts p in the prefix and Finset.le_sup gives Pn(x)>=p. Thus Pn(x)->infinity. The unconditional prime_number_limits.2 at x and Pn(x), together with theta(Pn)=theta(x), gives exactly Pn/x=(theta(x)/x)/(theta(Pn)/Pn)->1. Logarithmic continuity at 1 gives log(Pn/x)->0, and division by log(x)->infinity yields log(Pn)/log(x)->1. The square-root ratio and this logarithmic ratio give D(Pn)/D(x)->1. The all-real B envelope bounds abs(D(x)*B(x)) by abs(M)+3, so D(Pn)*B(Pn)-D(x)*B(x)=(D(Pn)/D(x)-1)*D(x)*B(x)->0. All denominators are justified eventually by x>1 and Pn>=2. No prime-gap estimate or Fourier transport of nearby endpoints enters this construction.

For arbitrary original records, ActualPriceRecordPrimeStructure gives exact initial prime support. OriginalEndpointPrimeTail.tail_robin_data then gives robinLogMargin(m)=B(P)+C(m), where the canonical FullArithmeticCorrectionSecondOrder.correction is C(m)=tail(m)+log(log(log(m)))-log(log(theta(P))). The public price_record_full_arithmetic_correction_second_order supplies a threshold 1<T0. At second-order tolerance 1, it bounds abs(log(P)*(D(P)*C(m)-2*sqrt(2))+d)<1, d=sqrt(2)*(2+log(2)). Choose T>=max(T0,2,exp(1+(1+abs(d))/eta)); division by the positive log(P) gives abs(D(P)*C(m)-2*sqrt(2))<eta uniformly before m and lambda are chosen.

For the universal lower bound take eta=epsilon/2 for both the real B envelope and fullC, then add the signed inequalities for the SAME integer m. For sharp attainment first choose the fullC threshold at epsilon/3 and the prime-normalization transfer threshold at epsilon/3, and a further x threshold ensuring Pn(x)>=max(TC,Y+1). Only THEN invoke arbitrarily-late real-B attainment at epsilon/3. Construct the cutoff record at this x. Its exact P is Pn(x), and the identity D(P)*margin(m)-K=[D(x)*B(x)+2+M]+[D(P)*B(P)-D(x)*B(x)] +[D(P)*C(m)-2*sqrt(2)] pays the three additional transfer budgets. The real-B attainment argument also separates the arithmetic, phase and WholeFormula residual errors.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.B_prefix`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.K`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn_atTop`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.cutoff_record`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.fullC_leading`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.margin_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.normalization`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](../../GoldenResource/GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure](../ActualPriceRecordPrimeStructure.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](../Analytic/RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff](ActualBalancedCutoff.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder](FullArithmeticCorrectionSecondOrder.md)
