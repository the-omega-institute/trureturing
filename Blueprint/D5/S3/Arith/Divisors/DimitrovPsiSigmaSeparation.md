# Prime separation for (ψ+σ)/(φ+σ)

## Abstract

For every n ≥ 2, (ψ(n)+σ(n))/(φ(n)+σ(n)) ≥ (n+1)/n, with equality exactly at the primes.

**Theorem 1.1 (The separation inequality).**

Lean statement: `D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation.separation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation.separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n ≥ 2 and put u=φ(n), v=ψ(n) (Dedekind psi) and w=σ(n). Then (v+w)/(u+w) ≥ (n+1)/n, with equality if and only if n is prime; this is the separation used for S. Dimitrov's Conjectures 2 and 7 (arXiv:2606.12484). Cross-multiplying, the claim is (n+1)u+w ≤ nv. For a prime p the three values are p−1, p+1 and p+1, and both sides equal p(p+1). Otherwise write n=pm with p the least prime factor, so 2 ≤ p ≤ m. The m multiples of p below n are not coprime to n, so u ≤ n−m. Every proper divisor d of n has n/d ≥ p, so d ≤ m; there are at most m of them, and w ≤ n+m². With v ≥ n+1 this gives (n+1)u+w ≤ (n+1)(n−m)+n+m², which is n(n+1)−(n−m)(m−1) < n(n+1) ≤ nv.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation.separation`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
