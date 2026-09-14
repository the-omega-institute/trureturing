# The OEIS A129598 Differing-Position Conjecture

## Abstract

The value 60 refutes Karttunen's A089966 characterization of A129598 differences.

**Definition 1.1 (The gcd-totient map).**

$$\forall m \in \mathrm{Nat},\; \operatorname{g}\left(m\right) = \operatorname{gcd}\left(m, \operatorname{totient}\left(m\right)\right)$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.g` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

For each natural m, g(m) is the greatest common divisor of m and Euler's totient of m.

**Definition 1.2 (The greatest-prime-factor function).**

$$\forall n \in \mathrm{Nat},\; \operatorname{greatestPrimeFactor}\left(n\right) = \operatorname{getLastD}\left(\operatorname{primeFactorsList}\left(n\right), 0\right)$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.greatestPrimeFactor` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

The prime factors are listed with multiplicity in increasing order. The last entry is the greatest prime factor, with default zero when the list is empty.

**Definition 1.3 (The A129598 sequence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{if}\left(n = 1, 2, n \cdot \operatorname{greatestPrimeFactor}\left(n\right)\right)$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.a` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

The initial value is a(1)=2. At every other natural n, a(n) is n times its greatest prime factor.

**Definition 1.4 (The A050399 sequence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{b}\left(n\right) = \operatorname{if}\left(\exists m \in \mathrm{Nat},\; (0 < m) \land (\operatorname{g}\left(m\right) = n), \operatorname{sInf}\left(\{m \in \mathrm{Nat} \mid ((0 < m) \land (\operatorname{g}\left(m\right) = n))\}\right), 0\right)$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.b` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

When a positive preimage of n under g exists, b(n) is the least such natural number; Nat.find supplies that least element. If the existence condition fails, the definition returns zero.

**Definition 1.5 (Membership in A089966).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{inA089966}\left(n\right)) \Leftrightarrow ((n = 1) \lor ((0 < n) \land (\operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right) = \operatorname{greatestPrimeFactor}\left(n\right) \bmod \operatorname{minFac}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.inA089966` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

Membership holds at one, or at a positive n when the number of distinct prime factors equals the greatest prime factor modulo the least prime factor.

**Definition 1.6 (Karttunen's differing-position characterization).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 < n) \Rightarrow ((\operatorname{a}\left(n\right) \ne \operatorname{b}\left(n\right)) \Leftrightarrow (\operatorname{inA089966}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.claim` (`✓ std3`).

*Citation.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

For every natural n greater than one, the characterization identifies a(n) and b(n) as unequal exactly at the members of A089966.

**Theorem 1.7 (The characterization fails at 60).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a129598-gcd-totient-position-refutation` (refuted) by `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a129598-gcd-totient-position-refutation","declaration_gid":"D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2007). *OEIS A129598, a(n) = n * A111089(n)*. URL: <https://oeis.org/A129598>.

*Commentary.*

At n=60, a(60)=300 has gcd-totient value 20 rather than 60, while b(60) has gcd-totient value 60 because 900 supplies a positive preimage. Thus a(60) and b(60) differ, but 60 is not in A089966. This refutes only the differing-position characterization; Conjecture 2 is untouched.

## References

- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.a`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.b`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.claim`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.g`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.greatestPrimeFactor`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.inA089966`
- Truth anchor: `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.result`
