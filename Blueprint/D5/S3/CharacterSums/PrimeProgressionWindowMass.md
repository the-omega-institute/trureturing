# Prime mass in power windows of a fixed arithmetic progression

## Abstract

A lower bound for the logarithmic prime mass in every sufficiently large real window

Fix a positive integer m and an invertible residue a modulo m. Write W(m,a,T) for the sum of (log p)/p over primes p congruent to a modulo m in the interval exp(T/2) < p ≤ exp(T). Write φ(m) for Euler's totient.

**Theorem 1.1 (Lower bound on each sufficiently large real window).**

$$\exists U \in \mathbb{R},\; \forall T \in \mathbb{R},\; U \le T \Rightarrow \frac{T}{21633248000 \phi(m)} \le \operatorname{W}\left(m, a, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/PrimeProgressionWindowMass.prime_progression_window_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer j, multiply the sum of (log p)/p times p raised to −jh over all primes p congruent to a by h. As h tends to zero from above the result approaches 1/(jφ(m)). This follows from the continuous regular part of the progression's Mangoldt series at one. Higher prime powers have summable total logarithmic weight, so their scaled contribution tends to zero.

Set t = exp(−log p/T). The polynomial t¹²(1−t)¹²(t−3/8)(3/5−t) is bounded above by the indicator of the window. It is positive only for 3/8 < t < 3/5, inside exp(−1) < t < exp(−1/2), and there it is at most one.

Combining the scaled moments at h = 1/T for degrees 12 through 26 gives the limit 1/(10816624000 φ(m)) for the normalized polynomial sum. The normalized window mass is at least that sum and hence eventually exceeds half its limit. For m = 8 the resulting lower bound is T/86532992000.

## References

- Truth anchor: `D5/S3/CharacterSums/PrimeProgressionWindowMass.prime_progression_window_mass`
