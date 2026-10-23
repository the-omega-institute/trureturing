# Divisor objective core

## Abstract

General divisor and prime-local resource objectives.

**Theorem 1.1 (The reciprocal divisor sum).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \sum_{d \in divisors\left(n\right)} \frac{1}{d} = \frac{sigma\left(1, n\right)}{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ObjectiveCore.reciprocal_divisor_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural n, pairing d with n/d identifies the sum of reciprocal divisors with sigma(1,n)/n. Both fractions are real. This identity is also consumed by SigmaNeighbourPeak.

**Definition 1.2 (The resource objective).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; goldenResourceObjective\left(lambda, n\right) = log\left(\sum_{d \in divisors\left(n\right)} \frac{1}{d}\right) - lambda \cdot log\left(n\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/ObjectiveCore.goldenResourceObjective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is J_lambda(n) = W(n) - lambda E(n) from theorem 11.1 of ZECKENDORF_EULER_5040, with the volume's definitions W(n) = ln(sum of reciprocal divisors) and E(n) = ln(n) expanded. The function is defined on all natural numbers; the optimum theorem uses positive natural numbers. Here divisors is Nat.divisors, log is Real.log, and natural numbers inside logarithms and fractions are coerced to real numbers. All displayed fractions denote real division.

**Lemma 1.3 (The divisor-sum expression).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; 1 \le n \Rightarrow goldenResourceObjective\left(lambda, n\right) = log\left(\frac{sigma\left(1, n\right)}{n}\right) - lambda \cdot log\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ObjectiveCore.golden_resource_sigma_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here sigma is ArithmeticFunction.sigma; sigma(1,n) is the sum of the positive divisors of n. The divisor-complement bijection identifies the reciprocal divisor sum with sigma(1,n)/n. This named companion connects the source definition to the multiplicative sigma API used in the proof of the unique optimum.

**Definition 1.4 (The one-prime local objective).**

$$\forall lambda \in \mathbb{R}, p \in \mathbb{N}, a \in \mathbb{N},\; goldenPrimeLocalObjective\left(lambda, p, a\right) = log\left(\frac{1 - (\frac{1}{p})^{a + 1}}{1 - (\frac{1}{p})}\right) - lambda \cdot a \cdot log\left(p\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/ObjectiveCore.goldenPrimeLocalObjective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real price lambda, natural base p, and natural exponent a, this is the logarithm of the reciprocal geometric factor through layer a, minus lambda times a log p. The definition is total; the optimality threshold theorem restricts p to be prime.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ObjectiveCore.goldenPrimeLocalObjective`
- Truth anchor: `D5/S3/Arith/GoldenResource/ObjectiveCore.goldenResourceObjective`
- Truth anchor: `D5/S3/Arith/GoldenResource/ObjectiveCore.golden_resource_sigma_identity`
- Truth anchor: `D5/S3/Arith/GoldenResource/ObjectiveCore.reciprocal_divisor_sum`
