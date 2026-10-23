# Golden Resource Optimal Layer Count

## Abstract

At a positive price, strictly profitable layer counts are the prime exponents of a positive optimizer that divides every positive optimizer.

**Theorem 1.1 (The active prime-layer set is finite).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow Finite\left(\{(p,k): \mathbb{N}\times\mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_part_sum_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive lambda, all pairs consisting of a prime and a positive exponent with marginal strictly above lambda form a finite set. The frozen attainment theorem supplies an optimizer. Its boundary threshold bounds each active exponent, embedding all active pairs in a finite union of factorization intervals. This finite set supplies the support of the integer constructed below.

**Definition 1.2 (Count of strictly profitable layers).**

$$\forall lambda \in \mathbb{R}, p \in \mathbb{N},\; optimalLayerCount\left(lambda, p\right) = ncard\left(\{k: \mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimalLayerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the natural cardinality of the positive layers above the price, with primality included in the predicate. Nonprime directions therefore have count zero. The definition accepts every real price; the following specifications require a strictly positive price.

**Theorem 1.3 (Active layers form the counted initial interval).**

$$\forall lambda \in \mathbb{R}, p \in \mathbb{N},\; \left(0 < lambda \land Prime\left(p\right)\right) \Rightarrow \{k: \mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\} = Icc\left(1, optimalLayerCount\left(lambda, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_layers_eq_count_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime and positive price, strict marginal decrease makes the finite active fiber downward closed among positive exponents. Taking its maximum and counting the resulting interval shows that the fiber is exactly the interval from one through its count.

A reference-inventory application uses the real clock t>1 and lambda(t)=1/(t log(t)). To compare a higher layer, put x=1/p for a prime p and let k>=2. Then 0<x<1 and k(1-x)>=1. Writing u=x^k(1-x)/(1-x^k)>0, the strict reciprocal form of Mathlib's Real.log_lt_sub_one_of_pos gives log(1+u)>u/(1+u)=x^k(1-x)/(1-x^(k+1)) >x^k(1-x)>=x^k/k. Hence goldenLayerMarginal(p,k) >1/(k p^k log(p)), including p=k=2. If p^k<=t, p^k log(p^k)<=t log(t), so lambda(t) is at most this reference price. The interval equality therefore implies k<=optimalLayerCount(lambda(t),p), including p^k=t.

For the first layer, reuse FirstLayerMarginalAntitone's golden_layer_marginal_one_eq_log_one_add_inv: the marginal is log(1+1/p)/log(p). The same reciprocal logarithm inequality gives 1/((p+1)log(p))<goldenLayerMarginal(p,1). If p<=t-1, positivity and p+1<=t imply lambda(t)<=1/((p+1)log(p)), so the first layer is active. Only primes in (t-1,t] can be missing reference first layers. For t>=5040, (p,k)=(2,4),(3,2) satisfy the higher-layer conditions, and p=5,7 satisfy the first-layer condition. The four counts are therefore at least 4,2,1,1.

**Theorem 1.4 (A simultaneous optimizer with minimal prime exponents).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\exists n \in \mathbb{N},\; 1 \le n \land \left(\left(\forall p \in \mathbb{N},\; factorization\left(n, p\right) = optimalLayerCount\left(lambda, p\right)\right) \land \left(IsGoldenResourceOptimal\left(lambda, n\right) \land \left(\forall m \in \mathbb{N},\; \left(1 \le m \land IsGoldenResourceOptimal\left(lambda, m\right)\right) \Rightarrow n \mid m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimal_layer_count_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive lambda there is a positive integer n whose factorization at every natural p equals the strict-gain layer count. It maximizes the resource objective and divides every positive optimizer, so each prime exponent is minimal.

The finite pair set projects to a finite prime support. The product of these prime powers realizes all counts simultaneously. The count interval gives the next-layer upper threshold and the strict last-layer lower threshold; the frozen global criterion then proves optimality. Every other optimizer must contain all strictly profitable layers, yielding divisibility.

Equality-price layers are excluded from this minimal configuration. Other optimizers at critical prices are allowed. In the following application, N is any positive integer optimal at the same price lambda(t)=1/(t log(t)); t is the price clock, not log(N). The simultaneous count realization n divides this same N. Thus every forced prime-power layer in n is also present in N.

Let m=floor(t)>=1. For every prime p, each positive reference exponent with p^k<=m-1 is active: k>=2 uses the higher-layer comparison, while k=1 uses p<=m-1<=t-1. Mathlib's Nat.factorization_lcmUpto identifies the exponent in lcmUpto(m-1) with Nat.log(p,m-1); Nat.pow_log_le_self and the count interval bound these exponents by those of n. Consequently lcmUpto(m-1) divides n and N. For m=1 this LCM is one, so the argument also covers 1<t<2.

Use the standard Mathlib Chebyshev.psi, the sum of von Mangoldt values through floor(t). Its psi_eq_log_lcmUpto identity gives psi(m-1)<=log(N). The last jump is exactly psi(t)-psi(m-1)=Lambda(m)<=log(m)<=log(t), where Lambda is ArithmeticFunction.vonMangoldt. Hence every such N satisfies log(N)>=psi(t)-log(t). For the minimal count realization, K(t)=log(n) is its actual strict-layer log inventory, so K(t)-psi(t)>=-log(t). Actual additional layers have not been discarded or replaced by a hypothetical configuration.

At every clock t>=5040 there is a finite anchor. A prime p<=5040 must be at most 5039, since 5040 is composite, so its first layer is active. Every higher reference prime power through 5040 is active as well. Thus lcmUpto(5040) divides every positive optimizer N at lambda(t). In particular 5040=2^4*3^2*5*7 divides N and log(N)>=psi(5040), including the clock t=5040. This does not identify 5040 itself as an optimizer at lambda(5040).

These are applications of the existing count and optimizer results with the stated Mathlib logarithm, LCM and Chebyshev identities; they introduce no independent mathematical declarations. A pointwise inventory lower bound does not establish the centered signed-von-Mangoldt estimate on an actual selected source, a bound for the least Robin counterexample, or the Robin inequality for all integers above 5040. RH remains open.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimalLayerCount`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimal_layer_count_spec`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_layers_eq_count_interval`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_part_sum_finite_support`
- Dependency: [D5/S3/Arith/GoldenFutureExtensionMaximum](../GoldenFutureExtensionMaximum.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](GoldenResourceThresholdCriterion.md)
