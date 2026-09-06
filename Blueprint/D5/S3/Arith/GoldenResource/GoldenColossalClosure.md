# Golden Colossal Closure

## Abstract

The base's worst adopted layer fixes a positive threshold. Retaining its factors and every strictly better layer constructs a colossally abundant multiple that divides every other colossally abundant multiple.

**Definition 1.1 (Base threshold).**

$$\forall B \in \mathbb{N},\; goldenPriceThreshold\left(B\right) = goldenLowerPrice\left(B\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenColossalClosure.goldenPriceThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold is exactly the frozen goldenLowerPrice. For B greater than one this is the minimum adopted-layer marginal over its prime divisors, and it is strictly positive.

**Theorem 1.2 (A multiple's support price is bounded by the base threshold).**

$$\forall B \in \mathbb{N}, N \in \mathbb{N}, lambda \in \mathbb{R},\; \left(1 < B \land \left(1 \le N \land \left(B \mid N \land \left(IsColossallyAbundant\left(N\right) \land \left(0 < lambda \land IsGoldenResourceOptimal\left(lambda, N\right)\right)\right)\right)\right)\right) \Rightarrow lambda \le goldenPriceThreshold\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenColossalClosure.support_price_le_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-price criterion bounds the supporting price by each last adopted layer of N. Divisibility makes every exponent of B at most the exponent of N; decreasing marginals then bound that same price by each last layer of B. Taking the finite minimum gives the threshold bound. The intermediate theorem requires N at least one. The final theorem handles N equal to zero separately, since the frozen abundance predicate does not itself assert positivity.

**Definition 1.3 (Strictly profitable layer count).**

$$\forall B \in \mathbb{N}, p \in \mathbb{N},\; goldenPositiveLayerCount\left(B, p\right) = ncard\left(\{k: \mathbb{N} \mid 1 \le k \land goldenPriceThreshold\left(B\right) < goldenLayerMarginal\left(p, k\right)\}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenColossalClosure.goldenPositiveLayerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the natural cardinality of the positive layer indices whose marginal is strictly greater than the base threshold. For a prime and B greater than one, the proof identifies this set with the finite interval from one to the first exponent whose next layer is no longer strictly better. Layers tied with the threshold are excluded from this count.

**Definition 1.4 (Threshold closure).**

$$\forall B \in \mathbb{N},\; 1 < B \Rightarrow colossalClosure\left(B\right) = \prod_{p \in Primes\left(\right)} p^{max\left(factorization\left(B, p\right), goldenPositiveLayerCount\left(B, p\right)\right)}$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossalClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For B greater than one, the closure is the finite prime product with exponent max(base exponent, strictly profitable layer count). The frozen uniform prime cutoff proves finite support, and the product is positive. For the out-of-source boundary inputs zero and one, the definition returns B itself.

**Theorem 1.5 (The construction has the specified exponents).**

$$\forall B \in \mathbb{N}, p \in \mathbb{N},\; \left(1 < B \land Prime\left(p\right)\right) \Rightarrow factorization\left(colossalClosure\left(B\right), p\right) = max\left(factorization\left(B, p\right), goldenPositiveLayerCount\left(B, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime, the factorization of the constructed integer is exactly the maximum of its base exponent and the natural cardinality of its strictly profitable layers. Thus the finite-support construction realizes the explicit threshold-count formula.

**Theorem 1.6 (The base divides its closure).**

$$\forall B \in \mathbb{N},\; 1 < B \Rightarrow B \mid colossalClosure\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenColossalClosure.dvd_colossal_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every closure exponent is at least its base exponent, so the natural-number factorization divisibility criterion proves that B divides its closure.

**Theorem 1.7 (The closure divides every abundant multiple).**

$$\forall B \in \mathbb{N}, N \in \mathbb{N},\; \left(1 < B \land \left(IsColossallyAbundant\left(N\right) \land B \mid N\right)\right) \Rightarrow colossalClosure\left(B\right) \mid N$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_dvd_of_dvd_colossally_abundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive abundant multiple N, the named support-price bound puts its supporting price at most the base threshold. Its next-layer bounds therefore bound every strictly profitable prefix by the exponent of N. Both entries of each maximum are at most that exponent, so the closure divides N. For N equal to zero, divisibility holds directly.

**Theorem 1.8 (The closure is colossally abundant).**

$$\forall B \in \mathbb{N},\; 1 < B \Rightarrow IsColossallyAbundant\left(colossalClosure\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_is_colossally_abundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the positive base threshold, every next layer of the closure has marginal at most the price. Each last adopted layer is either required by B, and hence has marginal at least the threshold, or is strictly profitable. The frozen common-price criterion proves global optimality. Equal-price layers are retained only as required by B. Numerical leastness and uniqueness are not separate public theorems in this slice.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossalClosure`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_dvd_of_dvd_colossally_abundant`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_factorization`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.colossal_closure_is_colossally_abundant`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.dvd_colossal_closure`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.goldenPositiveLayerCount`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.goldenPriceThreshold`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenColossalClosure.support_price_le_threshold`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval](GoldenResourcePriceInterval.md)
