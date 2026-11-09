# Kagey's Power-Product Conjecture Is False

## Abstract

The exponent coordinates of 12 and 72 refute eventual equality in A343881.

**Definition 1.1 (A power-product equation).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; Works\left(n, k, m\right) \Leftrightarrow (\exists c \in \mathrm{Nat},\; \exists x \in \mathrm{Nat},\; \exists y \in \mathrm{Nat},\; (0 < c) \land ((0 < x) \land ((0 < y) \land ((x < n) \land ((y < n) \land (k^{x} \cdot m^{y} = c^{n}))))))$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.Works` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343881, power-product minima and A064549*. URL: <https://oeis.org/A343881>.

*Commentary.*

Table read by antidiagonals upward: T(n,k) is the least integer m > k such that k^x * m^y = c^n for some positive integers c, x, and y where x < n and y < n; n >= 2, k >= 1. (OEIS A343881, NAME, revision 16; unpaginated.) All variables are natural numbers. Positivity of c, x and y and the strict bounds on both exponents are explicit.

**Definition 1.2 (The source's proposed value).**

$$\forall k \in \mathrm{Nat},\; A064549\left(k\right) = k \cdot \prod_{p \in \operatorname{Nat}.\operatorname{primeFactors}\left(k\right)} p$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.A064549` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343881, power-product minima and A064549*. URL: <https://oeis.org/A343881>.

*Commentary.*

a(n) = n * Product_{primes p|n} p. (OEIS A064549, NAME, revision 71; unpaginated.) The source index n is written k. Nat.primeFactors contains each prime divisor once.

**Definition 1.3 (The eventual-equality conjecture).**

$$claim \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 < k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall p \in \mathrm{Nat},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((N \le p) \Rightarrow ((\operatorname{if} h : (\exists m \in \mathrm{Nat},\; (k < m) \land (Works\left(p, k, m\right))) \operatorname{then} \operatorname{Nat}.\operatorname{find}\left(h\right) \operatorname{else} 0) = A064549\left(k\right)))))$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.claim` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343881, power-product minima and A064549*. URL: <https://oeis.org/A343881>.

*Commentary.*

Table read by antidiagonals upward: T(n,k) is the least integer m > k such that k^x * m^y = c^n for some positive integers c, x, and y where x < n and y < n; n >= 2, k >= 1. (OEIS A343881, NAME, revision 16; unpaginated.) Conjecture: T(p,k) = A064549(k) for fixed k > 1 and sufficiently large p. (OEIS A343881, COMMENT, revision 16; unpaginated.) For every natural k greater than one there is a threshold N such that the equality holds for every prime p at least N. Nat.find selects the least larger factor; the value is zero when no such factor exists.

**Theorem 1.4 (Refutation at k = 12).**

$$\neg (\forall k \in \mathrm{Nat},\; (1 < k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall p \in \mathrm{Nat},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((N \le p) \Rightarrow ((\operatorname{if} h : (\exists m \in \mathrm{Nat},\; (k < m) \land (Works\left(p, k, m\right))) \operatorname{then} \operatorname{Nat}.\operatorname{find}\left(h\right) \operatorname{else} 0) = A064549\left(k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result` (`✓ std3`). ∎

*Resolves.* `Problems/kagey343881-powerproducts` (refuted) by `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey343881-powerproducts","declaration_gid":"D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343881, power-product minima and A064549*. URL: <https://oeis.org/A343881>.

*Commentary.*

At k=12 the proposed value is 72. If 12^x times 72^y were an nth power, its prime coordinates would give n dividing both 2x+3y and x+2y. Twice the latter minus the former is y, so n divides y, contradicting 0<y<n. This obstruction holds for every natural n.

For a prime p a larger factor exists: 27 works at p=2, while 144 works at p at least 3 with exponents p-2 and 1. Thus the least factor itself satisfies Works and cannot be 72. There are primes beyond every threshold, which disproves the eventual equality. The universal equality T(p,12)=144 for primes p at least 7 and a corrected formula for arbitrary k remain unproved here. The separate assertion that prime rows contain distinct integers also remains unresolved.

## References

- Truth anchor: `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.A064549`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.Works`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.claim`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343881KageyPowerProducts.result`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](../../ConceptDynamics/InformationEscape/RegistrationTemplates.md)
