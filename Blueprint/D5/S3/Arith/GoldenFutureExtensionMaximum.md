# Golden Future Extension Maximum

## Abstract

At every positive resource price, the positive future layers above a positive integer form a finite prefix selection whose product attains the best extension gain.

**Theorem 1.1 (The future extension maximum is attained).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; \left(0 < lambda \land 1 \le n\right) \Rightarrow \left(\exists m \in \mathbb{N},\; n \mid m \land \left(1 \le m \land \left(\forall k \in \mathbb{N},\; \left(n \mid k \land 1 \le k\right) \Rightarrow goldenResourceObjective\left(lambda, k\right) - goldenResourceObjective\left(lambda, n\right) \le goldenResourceObjective\left(lambda, m\right) - goldenResourceObjective\left(lambda, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenFutureExtensionMaximum.golden_future_extension_maximum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real price lambda and positive natural number n, there is a positive multiple m of n whose resource-objective gain over n is at least that of every positive multiple k of n.

The proof constructs the finite set of exactly those future prime layers whose marginal exceeds lambda. Uniform decay across primes and fixed-prime decay bound this set in both coordinates, while strict marginal decrease makes each prime fiber a prefix. Its finite supremum defines a finitely supported factorization and therefore an actual positive integer m.

The arbitrary-price factorization theorem reduces the global comparison to prime-local comparisons. Positive prefix layers make the local objective nondecreasing up to the selected exponent, and every later layer has nonpositive gain, making it nonincreasing after that exponent.

This result proves only finite-prefix construction and attainment among positive divisible extensions. It does not identify the optimum with Phi_lambda or R_lambda, state the displayed layer-sum identity, or separately classify zero-marginal layers.

## References

- Truth anchor: `D5/S3/Arith/GoldenFutureExtensionMaximum.golden_future_extension_maximum_attained`
- Dependency: [D5/S3/Arith/GoldenPrimeLayerCofinite](GoldenPrimeLayerCofinite.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](GoldenResourceObjectiveFactorization.md)
