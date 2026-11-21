# Cancellation of products of two Jacobi symbols

## Abstract

Quadratic prime correlations on intervals in the class three modulo eight

Let C(p,r,A,L) be the sum of the products (p/n)(r/n) of Jacobi symbols over the integers A ≤ n < A + L with n congruent to 3 modulo 8. In the formula T denotes 8pr, and distinctOddPrimes(p,r) means that p and r are distinct odd primes.

**Theorem 1.1 (Complete-period cancellation and the interval remainder).**

$$\forall p \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall A \in \mathbb{N},\; \forall L \in \mathbb{N},\; \left(0 \le \operatorname{C}\left(p, p, A, L\right) \land \operatorname{C}\left(p, p, A, L\right) \le L\right) \land \left(\operatorname{distinctOddPrimes}\left(p, r\right) \Rightarrow \left(\operatorname{C}\left(p, r, A, T\right) = 0 \land \operatorname{abs}\left(\operatorname{C}\left(p, r, A, L\right)\right) \le \operatorname{mod}\left(L, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/QuadraticPrimeCrossPeriod.quadratic_prime_cross_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the selected residue class n is 3 modulo 4. Quadratic reciprocity therefore turns (p/n) and (r/n) into quadratic characters modulo p and r, with a sign that is fixed for each prime.

For distinct odd primes, the Chinese remainder theorem splits residues modulo 8pr into independent residues modulo 8, p and r. Any interval of length 8pr runs through all these residues. After fixing the first two coordinates, summing the nontrivial quadratic character over the field with r elements gives zero.

Delete complete periods from the interval. Each remaining product has absolute value at most one, so the remainder length bounds its sum. When the two arguments coincide, each retained summand is a square equal to zero or one.

## References

- Truth anchor: `D5/S3/CharacterSums/QuadraticPrimeCrossPeriod.quadratic_prime_cross_period`
