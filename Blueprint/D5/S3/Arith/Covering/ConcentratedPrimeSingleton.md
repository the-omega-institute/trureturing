# Concentrated Prime Singletons

## Abstract

In a distinct odd cover minimizing first class count and then modulus sum, concentration of one pure-prime class's private points forces an actual class of modulus three times that prime, with a unique residue among all original classes whose moduli contain the prime.

**Definition 1.1 (Private points of an original class).**

Lean statement: `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.Private`

*Formalization.* `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.Private` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural number is private to an original congruence class when it lies in that class and in no other original class.

**Theorem 1.2 (Concentration forces an original singleton).**

Lean statement: `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.concentrated_pure_prime_supplies_three_prime_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.concentrated_pure_prime_supplies_three_prime_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover every natural number by L congruence classes with pairwise distinct odd moduli greater than one. Assume L is no larger than the size of any such cover, and the sum of F's moduli is no larger than that of any such cover with L classes. Let p be any prime greater than three, and let g be an original class of modulus p. Suppose every private point of g is congruent to a fixed natural number a modulo three.

Then an original class j has modulus 3p and residue a modulo three. Moreover, every original class k whose modulus is divisible by p and whose residue agrees with j modulo p is equal to j. Prime exponents and other prime factors in the original moduli are unrestricted.

Count minimality gives each original class a private point: otherwise deleting that class produces a smaller cover. Prime-prefix transport then shows that every private point of every class with modulus divisible by p lies in the same residue a modulo three.

If modulus 3p is absent, the Chinese remainder theorem forces a class other than g whose modulus is divisible by p. Its odd modulus is strictly larger than 3p. Replacing it by the congruence class modulo 3p containing all its private points preserves coverage and distinctness, while strictly decreasing the modulus sum. Thus an original modulus 3p must occur. A private point identifies its residue modulo three. Any other original class whose modulus is divisible by p and whose residue agrees with it modulo p would have every private point covered by it, contradicting count minimality.

## References

- Truth anchor: `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.Private`
- Truth anchor: `D5/S3/Arith/Covering/ConcentratedPrimeSingleton.concentrated_pure_prime_supplies_three_prime_singleton`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/PrefixLiability](../Congruence/ConditionalComparison/PrefixLiability.md)
