# No Natural Prime Choice

## Abstract

Every natural prime is moved by an explicit permutation of the prime type, so the fully symmetric prime carrier has no globally distinguished element.

**Theorem 1.1 (No prime is fixed by every prime permutation).**

$$\forall p: Nat.Primes, \exists relabel: Equiv.\operatorname{Perm}(Nat.Primes), relabel(p) \neq p.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/NoNaturalPrimeChoice.no_prime_is_fixed_by_every_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary natural prime p, choose three when p is two and choose two otherwise. The chosen prime differs from p in both cases, and swapping the two prime values gives a permutation that moves p.

The construction is uniform over the selected prime. Thus the result rules out a common fixed point for the full permutation group; it does not merely exhibit one movable prime.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/NoNaturalPrimeChoice.no_prime_is_fixed_by_every_permutation`
