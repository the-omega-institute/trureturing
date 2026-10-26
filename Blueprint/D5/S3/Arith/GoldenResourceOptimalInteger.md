# Golden Resource Optimal Integer

## Abstract

At logarithmic resource price 1/25, the positive integer 5040 uniquely maximizes the logarithm of the reciprocal divisor sum minus the resource cost.

**Definition 1.1 (The marginal benefit per logarithmic unit).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N},\; goldenLayerMarginal\left(p, a\right) = \frac{log\left(\frac{1 - (\frac{1}{p})^{a + 1}}{1 - (\frac{1}{p})^{a}}\right)}{log\left(p\right)}$$

*Formalization.* `D5/S3/Arith/GoldenResourceOptimalInteger.goldenLayerMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the volume's r(p,a), written using powers of the real reciprocal of p. Its prime-layer interpretation applies when p is prime and a is positive; the Lean definition itself is total.

**Lemma 1.2 (Strictly decreasing prime layers).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N}, b \in \mathbb{N},\; (Prime\left(p\right) \land \left(1 \le a \land a < b\right)) \Rightarrow goldenLayerMarginal\left(p, b\right) < goldenLayerMarginal\left(p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceOptimalInteger.golden_layer_strict_decrease` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and positive layers a < b, the later layer has strictly smaller marginal benefit. Prime denotes Nat.Prime. The proof compares the two geometric quotients over positive denominators, then applies strict monotonicity of the real logarithm.

**Theorem 1.3 (5040 is the unique optimum at price 1/25).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (goldenResourceObjective\left(\frac{1}{25}, n\right) \le goldenResourceObjective\left(\frac{1}{25}, 5040\right) \land (goldenResourceObjective\left(\frac{1}{25}, n\right) = goldenResourceObjective\left(\frac{1}{25}, 5040\right) \Leftrightarrow n = 5040))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_unique_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural number n, its objective is at most that of 5040, with equality exactly when n = 5040. These two clauses state the unique argmax in theorem 11.1, without a bound on n.

The atom ends at the threshold table header. The surrounding volume supplies the rows for primes 2, 3, 5, 7 and the exclusion of primes at least 11. The proof verifies all nine strict rational power comparisons at exponent 25 in the kernel, proves uniform tail exclusion, and obtains the unique exponents 4, 2, 1, 1. Sigma factorization and a finite sum over the union of prime supports then give the global inequality and its equality characterization.

The result concerns this specified resource objective. It asserts neither the Riemann hypothesis nor optimality for other entropy or compression objectives.

## References

- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.goldenLayerMarginal`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.golden_layer_strict_decrease`
- Truth anchor: `D5/S3/Arith/GoldenResourceOptimalInteger.golden_resource_unique_optimum`
- Dependency: [D5/S3/Arith/GoldenResource/ObjectiveCore](GoldenResource/ObjectiveCore.md)
