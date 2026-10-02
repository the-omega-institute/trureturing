# A positive answer to the A400168 question

## Abstract

A400168 has a term above one: at n = 2^49 the term is two.

Antti Karttunen, OEIS A400168, revision 8: "Question: Are there terms greater than 1?" The entry defines a(n) = A235224(A003415(n)) - A400164(n), with offset one. It asks an existence question.

**Definition 1.1 (Indexed primorials).**

$$P\left(0\right) = 1 \land \left(\forall k \in \mathbb{N},\; P\left(k + 1\right) = primorial\left(nthPrime\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/OeisA400168PrimorialGap.P` (`✓ std3`).

*Citation.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

P(0) = 1. For k >= 1, P(k) is the product of the first k primes, as in A002110. nthPrime(k) is the zero-based enumeration Nat.nth Nat.Prime k. primorial(q) multiplies the primes at most q; hence primorial(nthPrime(k)) contains exactly the first k + 1 primes. Each new prime is at least two, so P is strictly increasing. The index of P counts primes and is not a prime-value bound.

**Definition 1.2 (Primorial length).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; L\left(m\right) = k \Leftrightarrow \left(m < P\left(k\right) \land \left(\forall j \in \mathbb{N},\; j < k \Rightarrow P\left(j\right) \le m\right)\right)$$

*Formalization.* `D5/S3/Arith/OeisA400168PrimorialGap.L` (`✓ std3`).

*Citation.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

L(m) is the least natural k with m < P(k). Such k exists for every m: P(m + 1) is at least nthPrime(m), which is at least m + 2. The least threshold definition has no finite search cap. P(0) = 1 gives L(0) = 0. For m > 0, L(m) = j + 1 precisely when P(j) <= m < P(j + 1). Strict increase then makes L(m) the largest k >= 1 with P(k - 1) <= m, exactly the NAME of A235224. In particular L(1) = 1. The displayed characterization includes zero and all positive arguments; minimality also implies monotonicity in m.

**Definition 1.3 (Arithmetic derivative).**

$$\forall n \in \mathbb{N},\; D\left(n\right) = sum\left(factorization\left(n\right), p \mapsto e \mapsto e \cdot NatDiv\left(n, p\right)\right)$$

*Formalization.* `D5/S3/Arith/OeisA400168PrimorialGap.D` (`✓ std3`).

*Citation.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

factorization(n) records the finite prime multiplicities v_p(n), and sum denotes Finsupp.sum over its support. NatDiv is natural integer division. Thus D(n) sums v_p(n) times n/p over exactly the primes dividing n. This is the factorization formula for A003415. For each summand p divides n, so division is exact. The empty factorizations give D(0) = D(1) = 0. Prime inputs give one, and addition of prime multiplicities for a product yields D(mn) = D(m)n + mD(n), including zero factors.

**Definition 1.4 (Maximum over prime-power divisors).**

$$\forall n \in \mathbb{N},\; M\left(n\right) = sup\left(filter\left(divisors\left(n\right), IsPrimePow\right), d \mapsto L\left(NatDiv\left(n, d\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/OeisA400168PrimorialGap.M` (`✓ std3`).

*Citation.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

divisors(n) is the finset of positive divisors, and filter retains precisely IsPrimePow divisors. On naturals IsPrimePow means p^e with p prime and e >= 1, matching A246655; one is excluded. sup is the maximum of the natural values, with zero for an empty finset. Hence M(1) = 0 and for every n >= 2, M(n) equals the A400164 maximum over all prime-power divisors d = p^e of L(n/d). No exponent or divisor is omitted, including d = n when n is a prime power. The harmless extension M(0) = 0 is outside the question's positive-index domain.

**Definition 1.5 (The universal negative answer).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow L\left(D\left(n\right)\right) \le M\left(n\right) + 1\right)$$

*Formalization.* `D5/S3/Arith/OeisA400168PrimorialGap.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

claim is the universal negative answer, not a conjecture asserted by Karttunen. For natural lengths, a(n) > 1 is equivalent to L(D(n)) > M(n) + 1, whether subtraction in the sequence is read as integer subtraction or natural subtraction. Negating the displayed universal statement is therefore equivalent to existence of a natural n >= 1 with a(n) > 1. This covers the complete original question, with all positive indices and the zero conventions in its component functions.

**Theorem 1.6 (The term at two to the forty-ninth power).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OeisA400168PrimorialGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400168-primorial-gap` (refuted) by `D5/S3/Arith/OeisA400168PrimorialGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400168-primorial-gap","declaration_gid":"D5/S3/Arith/OeisA400168PrimorialGap.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2026). *OEIS A400168: arithmetic derivative primorial length minus the prime-power-divisor maximum*. URL: <https://oeis.org/A400168>.

*Commentary.*

At n = 2^49 = 562949953421312, D(n) = 49 times 2^48 = 13792273858822144. Every prime-power divisor is 2^e with 1 <= e <= 49, so n/d <= 2^48, with equality at d = 2. P(12) = 7420738134810 <= 2^48 = 281474976710656 < 304250263527210 = P(13), giving M(n) = 13. P(14) = 13082761331670030 <= D(n) < 614889782588491410 = P(15), giving L(D(n)) = 15. Consequently a(n) = 15 - 13 = 2 > 1. The universal negative answer is false and the original existence question is answered yes. No least-index or infinite-family assertion is made.

## References

- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.D`
- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.L`
- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.M`
- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.P`
- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.claim`
- Truth anchor: `D5/S3/Arith/OeisA400168PrimorialGap.result`
