# The sharp window width

## Abstract

Keeping one auxiliary prime pair throughout a power window

Fix a prime q congruent to 3 modulo 8, write L = log q, and suppose L > 1. For b > 1, call W(q,b) the following property. For every real threshold R and every positive tolerance η there exist Y ≥ max(R,exp(5)), a loss 0 < ε < min(η,1/52), and a single prime d congruent to 7 modulo 16, valid at every real x in [Y,Yᵇ].

Write u = x^(ε/5). The bands are u/2 < log q ≤ u and u(log x)²/2 < log d ≤ u(log x)². The Jacobi symbols at q and at every odd prime p ≤ u equal 1 for numerator −d, and −d is 1 modulo 8. For every integer n from 1 to 2x^(2+8ε), log(4nqd) ≤ 2u(log x)².

**Theorem 1.1 (A strict width criterion).**

$$\forall q \in \mathbb{N},\; \left(\operatorname{Prime}\left(q\right) \land \left(\operatorname{mod}\left(q, 8\right) = 3 \land 1 < \operatorname{log}\left(q\right)\right)\right) \Rightarrow \left(\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\operatorname{W}\left(q, b\right) \Leftrightarrow b^{2}\operatorname{log}\left(q\right)^{b-1} < 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/MovingPrimeRowWidth.prime_pair_power_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the lower bound for log d at Yᵇ with the upper bound at Y. After cancellation, b² u(Y)^(b−1) < 2. Since L ≤ u(Y), equality at the claimed threshold already rules out a witness.

Conversely choose d arbitrarily large, split at q and all odd primes up to the ceiling of Lᵇ. Set a = √(log(d)/L), Y = exp(a), and ε = 5 log(L)/a. At x = exp(sa) with 1 ≤ s ≤ b, u = Lˢ and u(log x)²/log d = s² L^(s−1). This ratio lies in [1,2), and both prime size bands follow. Increasing d makes Y arbitrarily large and ε arbitrarily small. For log x ≥ 5 the spare u(log x)² in the conductor bound covers log(4nq).

This criterion proves the arithmetic row. The simultaneous character estimates and zero exclusions for the same pair, and comparison thresholds for a varying loss, remain separate analytic inputs.

## References

- Truth anchor: `D5/S3/CharacterSums/MovingPrimeRowWidth.prime_pair_power_window_iff`
- Dependency: [D5/S3/CharacterSums/SplitPrimeHostSeries](SplitPrimeHostSeries.md)
