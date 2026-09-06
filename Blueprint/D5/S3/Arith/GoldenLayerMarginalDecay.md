# Golden Layer Marginal Decay

## Abstract

Prime-layer marginals have a geometric upper bound and eventually fall below every positive price along each fixed prime direction.

**Theorem 1.1 (A geometric bound for every positive prime layer).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N},\; \left(Prime\left(p\right) \land 1 \le a\right) \Rightarrow goldenLayerMarginal\left(p, a\right) \le \frac{\frac{1}{p}^{a}}{log\left(p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenLayerMarginalDecay.golden_layer_marginal_le_inv_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and positive layer a, the marginal benefit is at most p to the negative a divided by log p.

The proof bounds log x by x minus one for the ratio of consecutive reciprocal geometric factors. Its algebraic core proves that this ratio minus one is at most p to the negative a.

**Theorem 1.2 (Only finitely many layers exceed a positive price at a fixed prime).**

$$\forall p \in \mathbb{N}, lambda \in \mathbb{R},\; \left(Prime\left(p\right) \land 0 < lambda\right) \Rightarrow \left(\exists N \in \mathbb{N},\; \forall a \in \mathbb{N},\; N \le a \Rightarrow goldenLayerMarginal\left(p, a\right) < lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenLayerMarginalDecay.golden_layer_marginal_lt_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed prime p and positive real price lambda, there is a natural cutoff N after which every layer marginal is strictly below lambda.

The geometric upper bound is consumed together with convergence of the powers of 1/p to zero. This theorem controls exponents at one fixed prime; it does not assert that only finitely many different primes can exceed the price.

## References

- Truth anchor: `D5/S3/Arith/GoldenLayerMarginalDecay.golden_layer_marginal_le_inv_pow`
- Truth anchor: `D5/S3/Arith/GoldenLayerMarginalDecay.golden_layer_marginal_lt_of_le`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](GoldenResourceOptimalInteger.md)
