# The first growth assertion of OEIS A222759

## Abstract

The prime threshold places the cubes of the first k primes below n.

**Definition 1.1 (One-based prime enumeration).**

$$\forall j \in \mathbb{N},\; P\left(j\right) = nth\left(Prime, j - 1\right)$$

*Formalization.* `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.P` (`✓ std3`).

*Citation.* T. D. Noe (2013). *OEIS A222759: first growth assertion for literal binomial remainders*. URL: <https://oeis.org/A222759>.

*Commentary.*

For j at least one, P(j) is the j-th prime, with P(1)=2. nth(Prime,t) denotes Mathlib's zero-based prime enumeration. The subtraction j-1 is natural subtraction; the unused extension P(0)=2 does not alter any positive index in the assertion.

**Definition 1.2 (The literal cubic remainder).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; cubicRemainder\left(n, q\right) = NatMod\left(choose\left(n \cdot q, q\right), q^{3}\right)$$

*Formalization.* `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.cubicRemainder` (`✓ std3`).

*Citation.* T. D. Noe (2013). *OEIS A222759: first growth assertion for literal binomial remainders*. URL: <https://oeis.org/A222759>.

*Commentary.*

choose(a,b) is the natural binomial coefficient. NatMod(a,m) is the least nonnegative remainder on division by a positive m, with NatMod(a,0)=a. Thus for a positive prime q, cubicRemainder(n,q) lies between zero and q cubed minus one. It is compared with the integer n itself.

**Theorem 1.3 (At least k distinct prime witnesses).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; 3 \le k \Rightarrow \left(1 \le n \Rightarrow \left(P\left(P\left(k\right)^{3}\right) \le n \Rightarrow \left(\exists q \in (Fin\left(k\right) \to \mathbb{N}),\; Injective\left(q\right) \land \left(\forall i \in Fin\left(k\right),\; 0 < q\left(i\right) \land \left(Prime\left(q\left(i\right)\right) \land cubicRemainder\left(n, q\left(i\right)\right) \ne n\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.result` (`✓ std3`). ∎

*Resolves.* `Problems/noe-2013-a222759-prime-cube-growth` (proved) by `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"noe-2013-a222759-prime-cube-growth","declaration_gid":"D5/S3/Arith/PrimeRemainders/OeisA222759Growth.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. D. Noe (2013). *OEIS A222759: first growth assertion for literal binomial remainders*. URL: <https://oeis.org/A222759>.

*Commentary.*

For every natural k at least three and every positive natural n at or above P(P(k)^3), the displayed injection supplies k distinct positive primes. Positive integers and positive naturals describe the same domain here. Fin(k) has indices 0 through k-1, and Injective is Function.Injective. The proof chooses q(i)=nth(Prime,i), the first k primes. Mathlib's Nat.add_two_le_nth_prime at t=j-1 gives P(j)>=j+1 for positive j. With j=P(k)^3, the threshold therefore implies P(k)^3<n, including equality n=P(P(k)^3) in the hypothesis. Nat.nth_injective and Nat.prime_nth_prime give distinct prime witnesses; Nat.nth_monotone gives q(i)<=P(k). Hence q(i)^3<=P(k)^3<n. Nat.mod_lt gives cubicRemainder(n,q(i))<q(i)^3<n, proving the required inequality. The argument uses the literal remainder range and needs no special binomial identity. It asserts the first growth clause for every k,n in its stated domain, without assuming that the full set of primes satisfying the predicate is finite.

## References

- Truth anchor: `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.P`
- Truth anchor: `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.cubicRemainder`
- Truth anchor: `D5/S3/Arith/PrimeRemainders/OeisA222759Growth.result`
