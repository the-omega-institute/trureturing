# Karttunen's divisor numerator parity identity

## Abstract

Karttunen's A378444 divisor count equals the ceiling of half A174273.

**Definition 1.1 (The rational prime-exponent sum).**

$$\forall n \in Nat,\; \operatorname{r}\left(n\right) = \operatorname{Finsupp}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{factorization}\left(n\right), (fun (p:Nat) \mapsto (fun (e:Nat) \mapsto \frac{(e:Rat)}{(p:Rat)}))\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.r` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A083345, NAME, revision 68 (unpaginated): “Numerator of r(n) = Sum(e/p: n=Product(p^e)); a(n) = n' / gcd(n,n'), where n' is the arithmetic derivative of n.” The function r is the displayed rational sum. Finsupp.sum ranges over the support of Nat.factorization; both casts in each quotient are to Rat. The empty sum gives r(1) = 0.

**Definition 1.2 (The reduced numerator).**

$$\forall n \in Nat,\; \operatorname{A083345}\left(n\right) = \operatorname{Rat}.\operatorname{num}\left(\operatorname{r}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A083345` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A378444, NAME, revision 14 (unpaginated): “a(n) is the number of divisors d of n such that A083345(d) is even, where A083345(n) is the numerator of Sum(e/p: n=Product(p^e)).” Rat.num is the reduced numerator with positive denominator, including Rat.num 0 = 0.

**Definition 1.3 (Divisors with even numerator).**

$$\forall n \in Nat,\; \operatorname{A378444}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (d:Nat) \mapsto \operatorname{A083345}\left(d\right) \bmod 2 = 0), \operatorname{Nat}.\operatorname{divisors}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A378444` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A378444, NAME, revision 14 (unpaginated): “a(n) is the number of divisors d of n such that A083345(d) is even, where A083345(n) is the numerator of Sum(e/p: n=Product(p^e)).” For n ≥ 1, Nat.divisors contains exactly the positive divisors. In particular d = 1 is counted because its numerator is zero. The residue here is an integer residue modulo 2.

**Definition 1.4 (Parity of the exponent at two).**

$$\forall n \in Nat,\; \operatorname{A035263}\left(n\right) = if (\operatorname{Nat}.\operatorname{factorization}\left(n, 2\right) \bmod 2 = 0) then 1 else 0$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A035263` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A035263, COMMENT, revision 266 (unpaginated): “a(n) is 1 if the number of trailing zeros in the binary representation of n is even.” For positive n this is the parity of Nat.factorization n 2. The residue here is a natural residue modulo 2.

**Definition 1.5 (The divisor transform).**

$$\forall n \in Nat,\; \operatorname{A174273}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{divisors}\left(n\right), (fun (d:Nat) \mapsto \operatorname{A035263}\left(d\right))\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A174273` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A174273, NAME, revision 17 (unpaginated): “Inverse Moebius transform of A035263.” This is the sum of A035263 over the positive divisors for n ≥ 1.

**Definition 1.6 (Karttunen's ceiling conjecture).**

$$claim = (\forall n \in Nat,\; (1 \le n) \Rightarrow (\operatorname{A378444}\left(n\right) = \operatorname{Nat}.\operatorname{ceil}\left(\frac{(\operatorname{A174273}\left(n\right):Rat)}{2}\right)))$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.claim` (`✓ std3`).

*Citation.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

OEIS A378444, FORMULA, revision 14 (unpaginated): “a(n) = ceiling(A174273(n)/2). [Conjectured] - _Antti Karttunen_, May 14 2025”. Its offset is 1. The variable n ranges over Nat with 1 ≤ n. The cast to Rat precedes division by 2; Nat.ceil equals the ordinary ceiling of this nonnegative rational.

**Theorem 1.7 (The ceiling identity holds for every positive integer).**

$$\forall n \in Nat,\; (1 \le n) \Rightarrow (\operatorname{A378444}\left(n\right) = \operatorname{Nat}.\operatorname{ceil}\left(\frac{(\operatorname{A174273}\left(n\right):Rat)}{2}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/karttunen-a378444` (proved) by `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karttunen-a378444","declaration_gid":"D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2025). *OEIS A378444: divisors with even reduced prime-exponent-sum numerator*. URL: <https://oeis.org/A378444>.

*Commentary.*

Write a divisor as 2^a times a product of odd prime powers. An odd common denominator shows that its reduced numerator is even exactly when a is even and a/2 plus the sum of the odd-prime exponents is even. Halving the even exponent at 2 identifies these divisors with exponent vectors in a finite rectangular box. The alternating sign sum of that box is a product of zeros and ones, so the number of even exponent sums is the ceiling of half its size. This includes 1, odd integers, powers of two and arbitrary mixed prime powers. The proof uses the inverse Moebius transform definition of A174273.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A035263`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A083345`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A174273`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.A378444`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.claim`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.r`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result`
