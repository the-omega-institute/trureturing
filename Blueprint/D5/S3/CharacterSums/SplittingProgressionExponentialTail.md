# Exponential decay of the exceptional fraction

## Abstract

Power saving for the two quadratic tests

Fix ε > 0 and a real number B. At a real height x set y = x^(ε/5), N = floor(x^400) and D = exp(y (log x)²). For 0 ≤ i < L let dᵢ = b + m(A+i). Both tests sum Λ(n) min(1,x/n) over 1 ≤ n ≤ N, weighted by J(n,dᵢ) and by J(n,q)J(n,dᵢ), respectively. The Jacobi symbol uses Mathlib's product over prime factors with multiplicity, including its value 1 for q = 0 or 1.

Write F(ε,x,q,b,m,A,L) for the number of indices where at least one absolute value exceeds x^(1/2+ε)/2. In the display e denotes ε. The predicate P(e,x,b,m,L) requires b ≡ 3 modulo 4, 4 dividing m, every prime divisor p of m satisfying p ≤ y or N < p, and D/(4 exp(4y)) ≤ L.

**Theorem 1.1 (Uniform exponential bound for failure of either test).**

$$\exists U \in \mathbb{R},\; \forall x \in \mathbb{R},\; U \le x \Rightarrow \left(\forall q \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{P}\left(e, x, b, m, L\right) \Rightarrow \operatorname{F}\left(e, x, q, b, m, A, L\right) \le L \operatorname{exp}\left(-B x^{\frac{e}{5}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_exponential_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing higher prime powers and prime divisors of m costs at most K√x + log 2 + θ(x^(1/2+ε/2)). At every sufficiently large height this is at most a quarter of x^(1/2+ε), uniformly for either twist.

Use the even moment 2k with k = floor(y log(x)/4800). By the Chinese remainder theorem the complete affine progression has independent residue coordinates. Each signed quadratic coordinate has mean zero and takes the values −1, 0, 1. For real weights aₚ its exponential average is bounded by exp(t²aₚ²/2), giving a complete mean moment at most 2(2 exp(1) k V)^k for V bounding the sum of the squared weights.

Expand both moments over the same tuples of primes. Each tuple contributes an endpoint error bounded by twice the product of its primes, allowing repetitions. Summing the absolute weighted errors costs at most 2(Σ p|aₚ|)^(2k). This is bounded by 2 exp(2400k log x), while the prescribed interval length grows on the scale exp(y(log x)²−O(y)). Counting indices above the remaining threshold and adding the two counts gives the bound. Selection of a prime denominator also requires enough primes in that progression.

**Theorem 1.2 (Power saving on the length scale D).**

$$\exists U \in \mathbb{R},\; \forall x \in \mathbb{R},\; U \le x \Rightarrow \left(\forall q \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{R}\left(e, x, b, m, L\right) \Rightarrow \operatorname{F}\left(e, x, q, b, m, A, L\right) \le L \operatorname{exp}\left(-c x^{\frac{e}{5}} {\operatorname{log}\left(x\right)}^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_power_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix ε > 0. In the display c denotes min(ε,1)/38400 and R has the same conditions as P with the allowed small-prime cap raised to x^(1/2+ε/2). With k as above, the complete moment gains a factor exponential in −k log x. The interval endpoint error is at most 2 exp(y(log x)²/2). Division by L and the test threshold gives the displayed bound. Since c(log x)² exceeds any fixed B eventually, this also gives the fixed-rate theorem.

## References

- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_exponential_tail`
- Truth anchor: `D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_power_tail`
- Dependency: [D5/S3/CharacterSums/JacobiTupleInterval](JacobiTupleInterval.md)
- Dependency: [D5/S3/CharacterSums/SplittingProgressionMangoldtSupply](SplittingProgressionMangoldtSupply.md)
