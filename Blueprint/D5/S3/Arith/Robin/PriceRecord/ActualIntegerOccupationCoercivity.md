# Actual integer occupation and the unrestricted objective defect

## Abstract

Quantitative second-layer occupation coercivity for every positive integer.

The estimate combines exact local integer-objective losses with uniform moving margins and the global prime-number-theorem error. The composition is repository-derived; no historical novelty or RH conclusion is asserted.

**Theorem 1.1 (The existing count optimizer is locally maximal).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.count_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.count_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real price lam, genuine prime p and exponent a, goldenPrimeLocalObjective(lam,p,a) is at most its value at optimalLayerCount(lam,p). Only private is removed from the original declaration; its type and proof are unchanged. The original layer-2 losses and the finite-gap extraction consume it here. The first-layer missing and occupied loss proofs consume it directly from this owner. This public exposure introduces no second local-maximality proof.

**Theorem 1.2 (Any finite set of prime local gaps is paid by the same actual defect).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.actual_local_gap_sum_le_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.actual_local_gap_sum_le_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>1, n>=1 and any finite set S of genuine primes, the sum over S of goldenPrimeLocalObjective(referencePrice(z),p,optimalLayerCount(referencePrice(z),p))-goldenPrimeLocalObjective(referencePrice(z),p,factorization(n,p)) is at most actualDefect(z,n). The proof is the single extraction of the existing unrestricted supremum/factorization argument. Both common_support_charge and actual_first_layer_charge consume it on their disjoint H union X. The unit, absent primes, primes beyond z and unbounded exponents remain in scope.

**Theorem 1.3 (A uniform quantitative estimate on arbitrary finite actual masks).**

$$\exists Z \in \mathbb{R},\; 2 \le Z \land \left(\forall z \in \mathbb{R},\; Z \le z \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\forall H \in Finset\left(\mathbb{N}\right), X \in Finset\left(\mathbb{N}\right),\; \left(\forall p \in \mathbb{N},\; p\in H \Rightarrow \left(Prime\left(p\right) \land \left(p \le sqrt\left(2\right) \cdot sqrt\left(z\right) \land factorization\left(n, p\right) \le 1\right)\right)\right) \Rightarrow \left(\left(\forall p \in \mathbb{N},\; p\in X \Rightarrow \left(Prime\left(p\right) \land \left(sqrt\left(2\right) \cdot sqrt\left(z\right) < p \land 2 \le factorization\left(n, p\right)\right)\right)\right) \Rightarrow \frac{\sum_{p\in H} log\left(p\right) + \sum_{p\in X} log\left(p\right)}{sqrt\left(z\right)} \le 6 \cdot sqrt\left(sqrt\left(z\right) \cdot log\left(z\right) \cdot actualDefect\left(z, n\right)\right) + 8 \cdot sqrt\left(z\right) \cdot log\left(z\right) \cdot actualDefect\left(z, n\right) + \frac{32}{log\left(z\right)}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.eventually_quantitative_actual_occupation_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the existing ActualReservePrimeMask.actualDefect(z,n) literally. The existing referencePrice(z) is 1/(z log z). The existing actualPressure(z) is the supremum of goldenResourceObjective(referencePrice(z),m) over ALL integers m >= 1, including the unit. Thus the defect is that same supremum minus the objective of the SAME n. The objective is the canonical log(sigma(n)/n) - log(n)/(z log z), by the existing objective identity. H and X are quantified finite sets, not newly defined global masks or masses.

H can contain any prime p <= sqrt(2) sqrt(z) with factorization(n,p) <= 1, including primes absent from n. X can contain any prime p > sqrt(2) sqrt(z) with factorization(n,p) >= 2. X has no upper cutoff: primes greater than z, arbitrarily large prime factors, and arbitrarily large exponents are included. The complete hole set is finite by its bounded real endpoint; the complete excess set is finite because exponent >= 2 implies membership in n.primeFactors. Both full masks are instances of this submask theorem. Disjointness follows from the opposite inequalities at the literal included lower cutoff.

Proof-to-code step 1: the consumed private local_step adapter applies GoldenLocalThreshold.golden_prime_local_objective_diff, normalizing only multiplication order. Its existing owner proof is reused after removal of private at that owner. count_maximal consumes positive_layers_eq_count_interval and golden_prime_local_objective_maximal_of_threshold. hole_loss uses monotonicity of the first marginal and the layer-2 increment. It treats exponents 0 and 1 explicitly. excess_loss uses golden_layer_strict_decrease and the same increment to show that all later included layers can only increase the loss. No exponent cap or strict-margin premise occurs in the target.

Proof-to-code step 2: actual_local_gap_sum_le_defect extracts the original common-support decomposition once. For any finite prime set S it obtains U from optimal_layer_count_spec at the positive price, and uses golden_resource_supremum_eq_positive_part_sum together with objective_at_optimal_eq_positive_part_sum to identify the EXISTING actualPressure with U's objective. On T = U.primeFactors union n.primeFactors union S, golden_resource_objective_sum_on makes actualDefect exactly the sum of local gaps. The count specification rewrites U's exponents to optimalLayerCount; count_maximal makes each gap nonnegative. Restricting to S proves the finite-gap bound. common_support_charge now consumes that extraction once on H union X, using the original hole_loss and excess_loss comparisons. The same public extraction is consumed by FirstPrimePrefixLocalization. A missing prime has exponent zero; primes greater than z remain included. U remains a proof witness, never a target premise.

Proof-to-code step 3: second_marginal identifies g2(p) = log(1 + 1/[p(p+1)]) and proves the needed bounds 1/(p^2+p+1) <= g2(p) <= p^(-2). The elementary log(1+u) <= u also gives the intermediate ordinary bound g2(p) <= 1/[p(p+1)] <= p^(-2). The code uses Real.one_sub_inv_le_log_of_pos for the lower estimate and the existing golden_layer_marginal_le_inv_pow for the upper estimate needed downstream. Dividing by the positive log p gives the actual layer-2 marginal.

Proof-to-code step 4: put L = log z, r = sqrt z, c = sqrt 2 for this exposition. eventual_geometry makes L >= 32 and c/r + 1/z <= 1/L. far_margins works simultaneously for EVERY real eta with 8/L <= eta <= 1/4. For p <= (c-eta)r, (c-eta)^2 <= 2-2eta, c r+1 <= z/L <= eta z/8, and log p <= L/2+1 <= (1/2+eta/8)L. Consequently (p^2+p+1) log p <= (1-eta/2) z L, and (1+eta/2)(1-eta/2) <= 1 yields marginal(p,2)-referencePrice(z) >= eta/(2zL). For p > (c+eta)r, log p >= L/2. With t=c+eta <=2, t^2 >= 2+(5/2)eta and (1-eta/2)t^2 >=2. The reciprocal square upper bound then gives referencePrice(z)-marginal(p,2) >= eta/(2zL). This last estimate is for ALL such primes, without p <= z.

Proof-to-code step 5: theta_error_log_power(2) supplies one GLOBAL real T such that for every y >= T, abs(theta(y)-y) <= y/log(y)^2. Both moving endpoints A=(c-eta)r and B=(c+eta)r are at least r, uniformly in eta. Thus eventual_geometry can require r >= T once, before quantifying eta. theta_window uses log A, log B >= L/2 and A+B=2cr to get theta(B)-theta(A) <= 2eta r + 8cr/L^2 <=4eta r. This is two applications of a global PNT error bound, not a short-interval PNT assumption.

Proof-to-code step 6: fixed_eta_bound filters H at p <= A and X at B < p. Their complements are disjoint selected primes in the literal interval A < p <= B. sum_log_interval bounds their sum by theta(B)-theta(A), using Chebyshev.theta_eq_sum_primesLE and finite sum_sdiff. The far charge and r^2=z give, with d=r L actualDefect(z,n), the bound (sum_H log p + sum_X log p)/r <= 4eta + 2d/eta for all 8/L <= eta <=1/4. Near primes are counted once.

Proof-to-code step 7: actual_reserve_prime_mask at the empty existing PrimeMask supplies nonnegativity of the SAME actualDefect, so d >= 0. clipped_optimization uses eta=max(8/L,sqrt d) when sqrt d <=1/4. Then eta <=8/L+sqrt d and d/eta <=sqrt d, giving 32/L+6sqrt d. When sqrt d>1/4, eta=1/4 gives 1+8d <=4sqrt d+8d. At d=0 the first choice is eta=8/L>0, so no division by sqrt 0 occurs. Adding the nonnegative remaining terms gives the displayed constants 6,8,32.

The residual 32/log z pays the finite-clock displacement of the exact second marginal from the unshifted sqrt(2)sqrt(z) cutoff. The argument does not claim a pure C sqrt d estimate at d=0, an effective numerical Z, sharp constants, a gap bound, a mass premise, an assumed optimizer, a support/exponent cap, or any RH or Robin conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.actual_local_gap_sum_le_defect`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.count_maximal`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.eventually_quantitative_actual_occupation_defect`
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](../../GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask](../../GoldenResource/ActualReserve/ActualReservePrimeMask.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
