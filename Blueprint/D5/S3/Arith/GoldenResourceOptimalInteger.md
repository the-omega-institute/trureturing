# Golden Resource Optimal Integer

## Abstract

At logarithmic resource price 1/25, the positive integer 5040 uniquely maximizes the logarithm of the reciprocal divisor sum minus the resource cost.

**Definition 1.1 (The resource objective).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; goldenResourceObjective\left(lambda, n\right) = log\left(\sum_{d \in divisors\left(n\right)} \frac{1}{d}\right) - lambda \cdot log\left(n\right)$$

*Formalization.* `D5/S3/Arith/GoldenResourceOptimalInteger.goldenResourceObjective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is J_lambda(n) = W(n) - lambda E(n) from theorem 11.1 of ZECKENDORF_EULER_5040, with the volume's definitions W(n) = ln(sum of reciprocal divisors) and E(n) = ln(n) expanded. The function is defined on all natural numbers; the optimum theorem uses positive natural numbers. Here divisors is Nat.divisors, log is Real.log, and natural numbers inside logarithms and fractions are coerced to real numbers. All displayed fractions denote real division.

**Definition 1.2 (The marginal benefit per logarithmic unit).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N},\; goldenLayerMarginal\left(p, a\right) = \frac{log\left(\frac{1 - (\frac{1}{p})^{a + 1}}{1 - (\frac{1}{p})^{a}}\right)}{log\left(p\right)}$$

*Formalization.* `D5/S3/Arith/GoldenResourceOptimalInteger.goldenLayerMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the volume's r(p,a), written using powers of the real reciprocal of p. Its prime-layer interpretation applies when p is prime and a is positive; the Lean definition itself is total.

**Lemma 1.3 (Strictly decreasing prime layers).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N}, b \in \mathbb{N},\; (Prime\left(p\right) \land \left(1 \le a \land a < b\right)) \Rightarrow goldenLayerMarginal\left(p, b\right) < goldenLayerMarginal\left(p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceOptimalInteger.golden_layer_strict_decrease` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and positive layers a < b, the later layer has strictly smaller marginal benefit. Prime denotes Nat.Prime. The proof compares the two geometric quotients over positive denominators, then applies strict monotonicity of the real logarithm.

**Lemma 1.4 (The divisor-sum expression).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; 1 \le n \Rightarrow goldenResourceObjective\left(lambda, n\right) = log\left(\frac{sigma\left(1, n\right)}{n}\right) - lambda \cdot log\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_sigma_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here sigma is ArithmeticFunction.sigma; sigma(1,n) is the sum of the positive divisors of n. The divisor-complement bijection identifies the reciprocal divisor sum with sigma(1,n)/n. This named companion connects the source definition to the multiplicative sigma API used in the proof of the unique optimum.

**Theorem 1.5 (5040 is the unique optimum at price 1/25).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (goldenResourceObjective\left(\frac{1}{25}, n\right) \le goldenResourceObjective\left(\frac{1}{25}, 5040\right) \land (goldenResourceObjective\left(\frac{1}{25}, n\right) = goldenResourceObjective\left(\frac{1}{25}, 5040\right) \Leftrightarrow n = 5040))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_unique_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural number n, its objective is at most that of 5040, with equality exactly when n = 5040. These two clauses state the unique argmax in theorem 11.1, without a bound on n.

The atom ends at the threshold table header. The surrounding volume supplies the rows for primes 2, 3, 5, 7 and the exclusion of primes at least 11. The proof verifies all nine strict rational power comparisons at exponent 25 in the kernel, proves uniform tail exclusion, and obtains the unique exponents 4, 2, 1, 1. Sigma factorization and a finite sum over the union of prime supports then give the global inequality and its equality characterization.

The result concerns this specified resource objective. It asserts neither the Riemann hypothesis nor optimality for other entropy or compression objectives.

## References

- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.goldenLayerMarginal`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.goldenResourceObjective`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.golden_layer_strict_decrease`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_sigma_identity`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_unique_optimum`
