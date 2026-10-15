# Golden Resource Supremum

## Abstract

At positive prices the resource supremum equals the finite sum of positive layer gains.

**Theorem 1.1 (Original prime-local telescoping identity).**

$$\forall lambda \in \mathbb{R}, p \in \mathbb{N}, a \in \mathbb{N},\; Prime\left(p\right) \Rightarrow goldenPrimeLocalObjective\left(lambda, p, a\right) = \sum_{k\in Icc\left(1, a\right)} log\left(p\right) \cdot (goldenLayerMarginal\left(p, k\right) - lambda)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.local_eq_layer_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original generic private proof is exposed in place for ActualReservePrimeMask. For every real price, actual prime and natural exponent, the local objective is the sum over k in Icc 1 a of log p times (goldenLayerMarginal p k - lambda). Exponent zero gives an empty sum. This visibility change preserves the original statement and proof.

**Theorem 1.2 (The objective at the minimal-count configuration).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; \left(0 < lambda \land \left(1 \le n \land \left(\forall p \in \mathbb{N},\; factorization\left(n, p\right) = optimalLayerCount\left(lambda, p\right)\right)\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n\right) = \sum_{(p,k)\in\{(p,k): \mathbb{N}\times\mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}} log\left(p\right) \cdot (goldenLayerMarginal\left(p, k\right) - lambda)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.objective_at_optimal_eq_positive_part_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive price and a positive integer realizing optimalLayerCount at every natural p, the objective equals the sum of log p times the net marginal over all strictly profitable prime-layer pairs. The frozen count specification supplies such an integer. The proof telescopes the public single-layer delta along each prime power, then regroups the finite active-pair set by prime. This is the value identity used by the supremum theorem.

**Theorem 1.3 (The exact unconstrained optimal value).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow sSup\left(\{x: \mathbb{R} \mid \exists n \in \mathbb{N},\; 1 \le n \land goldenResourceObjective\left(lambda, n\right) = x\}\right) = \sum_{(p,k)\in\{(p,k): \mathbb{N}\times\mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}} log\left(p\right) \cdot (goldenLayerMarginal\left(p, k\right) - lambda)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supremum ranges over objective values of all positive integers. The frozen count specification supplies a greatest element, so this supremum is attained and equals the objective evaluated in the preceding theorem.

The sum is indexed by the finite set of all pairs (p,k) with p prime, k at least one, and marginal strictly above lambda. Thus each included net marginal equals its positive part; all excluded positive-index prime layers have zero positive part. This finite support presentation expresses the positive-part double sum. The hypothesis lambda greater than zero is essential. No claim about nonpositive prices or the RH boundary is made.

A finite prime mask gives a useful actual-reserve application of these existing results. Fix a real x > 1 and set lambda_x = 1/(x log x). For a prime p let v_p(x) = max {k : p^k <= x}; this cutoff is inclusive. Write u_p(a) = log(sum from k=0 to a of p^(-k)) - lambda_x a log p, Q_p(a) = sum from k=1 to a of 1/(k p^k), and H_p(a) = Q_p(a) - lambda_x a log p. Define the complete finite reference F(x) = sum over primes p <= x of H_p(v_p(x)), J_x(n) = log(sigma(n)/n) - lambda_x log n for every n >= 1, and Psi(x) = sup over all n >= 1 of J_x(n). For a finite set S of primes put D(S) = sum over p in S of [1/p - log(1+1/p)] and L(S) = sum over p in S of 1/[2p(p+1)].

Assume p+1 <= x and 2x <= p^2 for every p in S. The first-layer price condition follows from lambda_x log p <= 1/x <= 1/(p+1) <= log(1+1/p). For the next layer, GoldenLayerMarginalDecay gives marginal(p,2) <= p^(-2)/log p <= lambda_x: indeed log x <= 2 log p and 2x <= p^2 imply x log x <= p^2 log p. GoldenLocalThreshold then gives u_p(a) <= u_p(1) for every natural exponent a. The same mask conditions give v_p(x)=1. Thus H_p(v_p(x))-u_p(a) >= 1/p-log(1+1/p). PrefixDeficitKernel.result at a=1 and z=1/p gives 1/[2p(p+1)] <= 1/p-log(1+1/p).

The entire complement is retained. ReferencePrefixDominance gives u_p(a) <= H_p(a). The increment of H_p at layer k is 1/(k p^k)-lambda_x log p; log monotonicity makes it nonnegative for p^k <= x and nonpositive above that inclusive cutoff. Consequently H_p(a) <= H_p(v_p(x)) for every prime and exponent. For any positive integer n, sum on the finite union of its prime support with the reference primes p <= x. Reference terms outside that reference set vanish because v_p(x)=0 there. GoldenResourceObjectiveFactorization identifies the actual sum with J_x(n), and every complementary prime contributes nonnegatively. This yields D(S) <= F(x)-J_x(n) for all n >= 1, without any assumption that the prime support of n is contained in S.

The positive price lambda_x has an attained unrestricted optimizer by GoldenResourceOptimalLayerCount. Applying the preceding bound at that optimizer gives L(S) <= D(S) <= R(x), where R(x)=F(x)-Psi(x). For every positive integer the remaining optimizer deficit d_n(x)=Psi(x)-J_x(n) is nonnegative, and F(x)-J_x(n)=R(x)+d_n(x). This application pays an explicit actual reserve using the project's 5040 objective machinery; it is a combined application of existing results. In a Robin explicit-formula argument at x=log n, the signed condition I_psi(x)+R(x)+d_n(x)>0 is still required. The mask estimate controls neither the sign nor the size of I_psi, and does not justify dropping d_n. It proves no new Robin counterexample floor or full Riemann hypothesis.

**Theorem 1.4 (Equality-price layers preserve the objective).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N}, p \in \mathbb{N},\; \left(1 \le n \land \left(Prime\left(p\right) \land goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right) = lambda\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n \cdot p\right) = goldenResourceObjective\left(lambda, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_objective_eq_of_layer_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real price, positive integer n and prime p, if the next p-layer has marginal equal to the price, n and n times p have equal objectives. Reading the equality in reverse also describes removal of that layer. This companion is a direct application of the frozen single-layer delta to the equality-price clause.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_objective_eq_of_layer_price`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.local_eq_layer_sum`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.objective_at_optimal_eq_positive_part_sum`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
