# Finite Prime Information Budget

## Abstract

A complete finite prime-power readout meets the exact base-two information budget.

**Theorem 1.1 (The prime-power precision sum bounds the window information).**

$$\forall S: \operatorname{Finset}(\operatorname{NatPrimes}), \kappa: \operatorname{NatPrimes} \to \operatorname{PNat}, N\in \mathbb{N},\\{}0 < N \land N \leq \prod_{p\in S} p^{\kappa(p)} \Rightarrow \\{}\operatorname{logb}(2, N) \leq \sum_{p\in S} \kappa(p) \operatorname{logb}(2, p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimeInformationBudget.finite_prime_information_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite set whose elements carry primality proofs, and let kappa assign every prime a positive natural precision. For a positive window size N, the public completeness premise states that N does not exceed the selected prime-power product.

The base-two logarithm is increasing on positive reals. Applying it to the completeness bound and expanding the logarithm of the finite product gives the sum of kappa(p) times logb(2,p), which is therefore at least logb(2,N).

The proof directly applies Real.logb_le_logb, Real.log_prod, and Real.log_pow from the pinned library. Prime and positive-precision restrictions are encoded in the public carriers rather than introduced by auxiliary definitions.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimeInformationBudget.finite_prime_information_budget`
