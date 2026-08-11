# Hilbert Monoid Non-Unique Factorization

## Abstract

The Hilbert monoid of naturals congruent to 1 mod 4 lacks unique factorization: 441 = 9*49 = 21*21 with 9, 21, 49 all H-irreducible.

**Theorem 1.1 (The Hilbert monoid has two distinct irreducible factorizations of 441).**

$$441=9\cdot49=21\cdot21$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/HilbertMonoidNonUnique.hilbert_monoid_factorization_not_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert monoid H consists of the positive naturals congruent to 1 mod 4, closed under multiplication. An element is H-irreducible when it lies in H, exceeds one, and admits only the trivial factorization into two H-elements. The numbers 9, 21, and 49 are all H-irreducible (their only proper natural divisors 3, 7 are congruent to 3 mod 4, hence outside H).

Then 441 = 9*49 = 21*21 exhibits two factorizations of 441 into H-irreducibles whose multisets of factors {9, 49} and {21, 21} differ, so factorization in H is not unique. This is the concrete witness behind the Euler-product criterion for freeness; no claim is made about the general product-count identity.

## References

- Truth anchor: `D5/S3/Factorization/HilbertMonoidNonUnique.hilbert_monoid_factorization_not_unique`
