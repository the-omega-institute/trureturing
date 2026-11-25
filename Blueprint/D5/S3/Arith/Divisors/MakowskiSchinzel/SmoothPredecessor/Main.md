# The sigma-totient inequality for smooth prime predecessors

## Abstract

The sigma-totient inequality for smooth prime predecessors

**Theorem 1.1 (Both inequalities under the predecessor condition).**

$$\forall n \in \mathbb{N},\; \left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(n\right) \Rightarrow q - 1 \in \operatorname{smoothNumbers}\left(98\right)\right) \Rightarrow \left(n \le 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\operatorname{Odd}\left(n\right) \Rightarrow n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Acknowledgement.* Carl Pomerance (2026). *A bound for the Mąkowski–Schinzel conjecture concerning the arithmetic functions σ and ϕ*. URL: <https://math.dartmouth.edu/~carlp/msconj2.pdf>.

*Commentary.*

For every natural n, suppose every prime divisor q of n has q-1 in the 98-smooth positive integers, so all prime divisors of q-1 are at most 97. Then n<=2 sigma(1,phi(n)), and odd n satisfies n<=sigma(1,phi(n)). There is no bound on n, q, or their exponents. The finite table covers the non-Fermat prime predecessors through one million. For a larger predecessor, its largest odd prime factor supplies a label; division by twice that label produces a smooth number beyond the corresponding finite cutoff. A common Euler-product estimate bounds the actual finite tail after the small smooth contribution is subtracted. Checked prefix products and this tail bound control each group. Fermat prime factors use the separate power-of-two totient inequality, without assuming that all Fermat primes are known. Radical and parity lifting recover both conclusions. Integers with an unrestricted predecessor prime factor above 97 are outside this statement; no conclusion about the unrestricted conjecture is asserted.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Main](../Main.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier](Frontier.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups](SmoothedGroups.md)
