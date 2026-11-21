# Logarithmic mass of primes subject to quadratic splitting

## Abstract

Divergent prime sums under simultaneous quadratic splitting conditions

For a natural cutoff B, D(B) consists of the primes d congruent to 7 modulo 16 such that the Jacobi symbol (−d/p) equals 1 for every odd prime p ≤ B. Q(d) consists of the primes q congruent to 3 modulo 8 with (−d/q) = 1. For the reverse order, T(B,q) consists of those d in D(B) for which q belongs to Q(d).

For each set S, M(S,X) sums (log n)/n over its elements n < X. In the formula, L(S) means that M(S,X) tends to positive infinity as the natural number X tends to infinity and that for every natural threshold N there is an element of S greater than N.

**Theorem 1.1 (Divergence in either order of prime selection).**

$$\forall B \in \mathbb{N},\; \operatorname{L}\left(\operatorname{D}\left(B\right)\right) \land \left(\left(\forall d \in \mathbb{N},\; d \in \operatorname{D}\left(B\right) \Rightarrow \operatorname{L}\left(\operatorname{Q}\left(d\right)\right)\right) \land \left(\forall q \in \mathbb{N},\; \left(\operatorname{Prime}\left(q\right) \land \operatorname{mod}\left(q, 8\right) = 3\right) \Rightarrow \operatorname{L}\left(\operatorname{T}\left(B, q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SplitPrimeHostSeries.split_prime_host_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

To select d, multiply the odd primes p ≤ B to obtain P. The Chinese remainder theorem gives a reduced progression modulo 16P that is 7 modulo 16 and −1 modulo P. Its prime terms have (−d/p) = 1. The empty product at B = 0 is 1.

For fixed d, use the reduced progression that is 3 modulo 8 and 1 modulo d. Then (q/d) = 1. Since q and d are both 3 modulo 4, the signs from reciprocity and from (−1/q) cancel to give (−d/q) = 1. In each case the logarithmic prime mass of one reduced progression diverges, and all additional terms are nonnegative.

If q is chosen first, use the discriminants for cutoff max(B,q). Every one of them passes the original splitting tests and the additional test at q. Their divergent mass therefore gives divergent mass in T(B,q).

## References

- Truth anchor: `D5/S3/Arith/SplitPrimeHostSeries.split_prime_host_series`
