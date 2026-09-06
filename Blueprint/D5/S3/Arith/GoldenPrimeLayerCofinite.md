# Golden Prime Layer Cofiniteness

## Abstract

At every positive price, all positive layer marginals lie below the price beyond one uniform prime cutoff.

**Theorem 1.1 (Only finitely many primes can support a profitable layer).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\exists P \in \mathbb{N},\; \forall p \in \mathbb{N}, a \in \mathbb{N},\; \left(Prime\left(p\right) \land \left(P \le p \land 1 \le a\right)\right) \Rightarrow goldenLayerMarginal\left(p, a\right) < lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenPrimeLayerCofinite.golden_layer_marginal_lt_of_prime_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real price lambda, there is a natural cutoff P such that every prime p at least P and every positive layer a have marginal benefit strictly below lambda.

The proof first shows that 1/p divided by log p tends to zero as p grows. It then consumes the frozen geometric marginal bound and the inequality (1/p)^a at most 1/p for every positive a. This controls the prime half of the atom's finiteness claim; the fixed-prime exponent half is carried by the preceding marginal-decay module.

## References

- Truth anchor: `D5/S3/Arith/GoldenPrimeLayerCofinite.golden_layer_marginal_lt_of_prime_le`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](GoldenLayerMarginalDecay.md)
