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

**Theorem 1.4 (A simultaneous optimizer with minimal prime exponents).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\exists n \in \mathbb{N},\; 1 \le n \land \left(\left(\forall p \in \mathbb{N},\; factorization\left(n, p\right) = optimalLayerCount\left(lambda, p\right)\right) \land \left(IsGoldenResourceOptimal\left(lambda, n\right) \land \left(\forall m \in \mathbb{N},\; \left(1 \le m \land IsGoldenResourceOptimal\left(lambda, m\right)\right) \Rightarrow n \mid m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimal_layer_count_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive lambda there is a positive integer n whose factorization at every natural p equals the strict-gain layer count. It maximizes the resource objective and divides every positive optimizer, so each prime exponent is minimal.

The finite pair set projects to a finite prime support. The product of these prime powers realizes all counts simultaneously. The count interval gives the next-layer upper threshold and the strict last-layer lower threshold; the frozen global criterion then proves optimality. Every other optimizer must contain all strictly profitable layers, yielding divisibility.

Equality-price layers are excluded from this minimal configuration. This statement allows other optimizers at critical prices. The positive-part formula for the optimal value, a full description of equality-price choices, and the 5040 boundary are outside this slice.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimalLayerCount`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.optimal_layer_count_spec`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_layers_eq_count_interval`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.positive_part_sum_finite_support`
- Dependency: [D5/S3/Arith/GoldenFutureExtensionMaximum](../GoldenFutureExtensionMaximum.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](GoldenResourceThresholdCriterion.md)
