# Bouras's unique prime occurrence conjecture is false

## Abstract

The prime 11 occurs at indices 10 and 21 in OEIS A372763.

**Definition 1.1 (The inner continued fraction).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Q},\; \operatorname{nested}\left(n, x\right) = \operatorname{List}.\operatorname{foldr}\left((\operatorname{fun} (k : \mathbb{N}) (t : \mathbb{Q}) \mapsto (k : \mathbb{Q}) - \frac{(k : \mathbb{Q}) + 1}{t}), x, (\operatorname{List}.\operatorname{range}'\left(2, (n - 2)\right))\right)$$

*Formalization.* `D5/S3/Arith/Primes/BourasA372763OnceRefutation.nested` (`✓ std3`).

*Citation.* M. Bouras (2024). *OEIS A372763: denominators of a continued fraction*. URL: <https://oeis.org/A372763>.

*Commentary.*

The right fold evaluates k - (k+1)/t for k = 2 through n-1, starting from x. All divisions in this expression are rational divisions. The subtraction n-2 in List.range' is truncated natural subtraction. For n at least three, this is the inner expression in OEIS A372763, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5)))))."

**Definition 1.2 (The reciprocal of the inner expression).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{Q},\; \operatorname{K}\left(n, x\right) = \frac{1}{\operatorname{nested}\left(n, x\right)}$$

*Formalization.* `D5/S3/Arith/Primes/BourasA372763OnceRefutation.K` (`✓ std3`).

*Citation.* M. Bouras (2024). *OEIS A372763: denominators of a continued fraction*. URL: <https://oeis.org/A372763>.

*Commentary.*

K takes the reciprocal of nested, with terminal rational value x. The rational operations are total, including division by zero; the two fractions used below have nonzero tails. OEIS A372763, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5)))))."

**Definition 1.3 (The denominator sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{Rat}.\operatorname{den}\left((\operatorname{K}\left(n, ((n : \mathbb{Q}) + 5)\right))\right)$$

*Formalization.* `D5/S3/Arith/Primes/BourasA372763OnceRefutation.a` (`✓ std3`).

*Citation.* M. Bouras (2024). *OEIS A372763: denominators of a continued fraction*. URL: <https://oeis.org/A372763>.

*Commentary.*

OEIS A372763, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5)))))." Rat.den is the positive denominator of the reduced rational number. The entry has offset three; the terminal value is the rational number n+5.

**Definition 1.4 (Conjecture 2).**

$$claim = (\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \ne 2 \Rightarrow \left(p \ne 3 \Rightarrow \exists! (n : \mathbb{N}), (3 \le n \land \operatorname{a}\left(n\right) = p)\right)\right))$$

*Formalization.* `D5/S3/Arith/Primes/BourasA372763OnceRefutation.claim` (`✓ std3`).

*Citation.* M. Bouras (2024). *OEIS A372763: denominators of a continued fraction*. URL: <https://oeis.org/A372763>.

*Commentary.*

OEIS A372763, COMMENTS (unpaginated): "Conjecture 2: Except for 2 and 3, all primes appear in the sequence once." The prime p ranges over the natural numbers. A unique occurrence means exactly one natural index n at least three with a(n)=p.

**Theorem 1.5 (The repeated prime 11).**

$$\neg (\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p \ne 2 \Rightarrow \left(p \ne 3 \Rightarrow \exists! (n : \mathbb{N}), (3 \le n \land \operatorname{a}\left(n\right) = p)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/BourasA372763OnceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bouras372763-once` (refuted) by `D5/S3/Arith/Primes/BourasA372763OnceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bouras372763-once","declaration_gid":"D5/S3/Arith/Primes/BourasA372763OnceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2024). *OEIS A372763: denominators of a continued fraction*. URL: <https://oeis.org/A372763>.

*Commentary.*

Exact rational evaluation gives a(10)=11 and a(21)=11. The natural number 11 is prime and differs from 2 and 3. Both indices are at least three and are unequal, so the asserted uniqueness fails. The repeated value already appears in the published OEIS data. This refutation does not assert an upper bound on its global number of occurrences or resolve Conjecture 1.

## References

- Truth anchor: `D5/S3/Arith/Primes/BourasA372763OnceRefutation.K`
- Truth anchor: `D5/S3/Arith/Primes/BourasA372763OnceRefutation.a`
- Truth anchor: `D5/S3/Arith/Primes/BourasA372763OnceRefutation.claim`
- Truth anchor: `D5/S3/Arith/Primes/BourasA372763OnceRefutation.nested`
- Truth anchor: `D5/S3/Arith/Primes/BourasA372763OnceRefutation.result`
