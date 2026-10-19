# The largest number neither dividing nor coprime to n

## Abstract

Mathar's A073759 conjecture holds for every natural index at least five.

**Definition 1.1 (OEIS A073759).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} m : \mathbb{N} \mapsto (\neg (m \mid n)) \land (\neg \operatorname{Nat}.\operatorname{Coprime}\left(m, n\right))), \operatorname{Finset}.\operatorname{Ico}\left(1, n\right)\right), id\right)$$

*Formalization.* `D5/S3/Arith/Primes/MatharA073759.a` (`✓ std3`).

*Citation.* R. J. Mathar (2026). *OEIS A073759: largest number neither a divisor of nor relatively prime to n*. URL: <https://oeis.org/A073759>.

*Commentary.*

OEIS A073759, NAME (unpaginated): "Largest number < n that is neither a divisor of nor relatively prime to n, or 0 if no such number exists." The candidates are the positive natural numbers m in Finset.Ico 1 n. Finset.filter keeps exactly those with neither m dividing n nor Nat.Coprime m n. Finset.sup id selects the largest candidate and is zero for the empty set. The entry has offset 1.

**Definition 1.2 (Subtracting the least prime factor).**

$$\forall n \in \mathbb{N},\; \operatorname{A046666}\left(n\right) = n - \operatorname{Nat}.\operatorname{minFac}\left(n\right)$$

*Formalization.* `D5/S3/Arith/Primes/MatharA073759.A046666` (`✓ std3`).

*Citation.* R. J. Mathar (2026). *OEIS A073759: largest number neither a divisor of nor relatively prime to n*. URL: <https://oeis.org/A073759>.

*Commentary.*

OEIS A046666, FORMULA (unpaginated): "a(n) = n - (smallest prime dividing n)." Nat.minFac is the least prime factor at every n at least two, the entry's offset. Subtraction is truncated natural subtraction.

**Definition 1.3 (Half the difference).**

$$\forall n \in \mathbb{N},\; \operatorname{A046667}\left(n\right) = \operatorname{Nat}.\operatorname{div}\left(\operatorname{A046666}\left(n\right), 2\right)$$

*Formalization.* `D5/S3/Arith/Primes/MatharA073759.A046667` (`✓ std3`).

*Citation.* R. J. Mathar (2026). *OEIS A073759: largest number neither a divisor of nor relatively prime to n*. URL: <https://oeis.org/A073759>.

*Commentary.*

OEIS A046667, FORMULA (unpaginated): "a(n) = A046666(n)/2." Nat.div is natural integer division, rounding down; the entry has offset 2.

**Definition 1.4 (Mathar's conjecture).**

$$claim = (\forall n \in \mathbb{N},\; (5 \le n) \Rightarrow (\operatorname{a}\left(n\right) = 2 \cdot \operatorname{A046667}\left(n\right)))$$

*Formalization.* `D5/S3/Arith/Primes/MatharA073759.claim` (`✓ std3`).

*Citation.* R. J. Mathar (2026). *OEIS A073759: largest number neither a divisor of nor relatively prime to n*. URL: <https://oeis.org/A073759>.

*Commentary.*

OEIS A073759, FORMULA (unpaginated): "Conjecture: a(n) = 2*A046667(n) if n>=5. - _R. J. Mathar_, May 15 2026". The quantifier ranges over all natural n at least five; a is A073759 and A046667 is defined above.

**Theorem 1.5 (The conjecture holds).**

$$\forall n \in \mathbb{N},\; (5 \le n) \Rightarrow (\operatorname{a}\left(n\right) = 2 \cdot \operatorname{A046667}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/MatharA073759.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-oeis-a073759-least-prime-factor` (proved) by `D5/S3/Arith/Primes/MatharA073759.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-oeis-a073759-least-prime-factor","declaration_gid":"D5/S3/Arith/Primes/MatharA073759.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar (2026). *OEIS A073759: largest number neither a divisor of nor relatively prime to n*. URL: <https://oeis.org/A073759>.

*Commentary.*

For prime n every positive k below n is coprime to n, so a(n) is zero. For composite n at least five, set p = Nat.minFac n. The inequality p squared at most n gives 2p < n. Thus n-p has gcd p with n, strictly smaller than n-p, and is neither a divisor of n nor coprime to n. A common prime divisor r of any k < n and n divides n-k, so p is at most r and r is at most n-k. This bounds every candidate by n-p. Finally n-p is even: an even n has p=2, and an odd n has odd p. Hence a(n)=n-p=2*A046667(n).

## References

- Truth anchor: `D5/S3/Arith/Primes/MatharA073759.A046666`
- Truth anchor: `D5/S3/Arith/Primes/MatharA073759.A046667`
- Truth anchor: `D5/S3/Arith/Primes/MatharA073759.a`
- Truth anchor: `D5/S3/Arith/Primes/MatharA073759.claim`
- Truth anchor: `D5/S3/Arith/Primes/MatharA073759.result`
