# Coprime prime-exponent normal form

## Abstract

A coprime residual admits an ordered prime-exponent representative with no smaller normalized divisor sum.

**Definition 1.1 (Allowed ordered residuals).**

$$AllowedOrdered$$

*Formalization.* `D5/S3/Arith/ExponentExchange/CoprimeNormalForm.AllowedOrdered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AllowedOrdered M m requires that, for every pair of distinct primes p<q coprime to M, the q-exponent of m is at most its p-exponent.

**Theorem 1.2 (Ordered representative of a coprime integer).**

$$existsCoprimeAllowedOrderedForm$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/CoprimeNormalForm.exists_coprime_allowed_ordered_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive n coprime to M has a positive m≤n that remains coprime to M, satisfies AllowedOrdered M m, and has normalized divisor sum at least that of n. The proof repeatedly swaps an inverted pair of prime exponents.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/CoprimeNormalForm.AllowedOrdered`
- Truth anchor: `D5/S3/Arith/ExponentExchange/CoprimeNormalForm.exists_coprime_allowed_ordered_form`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](IntegerSwap.md)
