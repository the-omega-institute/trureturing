# Browne's Chebyshev numerator and floor product

## Abstract

Every positive Chebyshev row numerator equals Browne's literal floor product and its radical sign.

The source is OEIS A164660, revision 19, FORMULA; it has no page numbers. Natural indices include zero, while the asserted equalities require a positive index. The Chebyshev polynomials and the natural radical are the Mathlib objects. Nat.div denotes natural integer division. The floors have values in the integers.

**Definition 1.1 (The rational row sum).**

$$\forall m \in \mathbb{N},\; rowSum\left(m\right) = \sum_{j \in \operatorname{Finset.Icc}\left(1, m + 1\right)} \frac{\operatorname{Polynomial.coeff}\left(\operatorname{Polynomial.Chebyshev.T}\left(\mathbb{Q}, (m: \mathbb{Z})\right), j - 1\right)}{(j: \mathbb{Q})}$$

*Formalization.* `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.rowSum` (`✓ std3`).

*Citation.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Commentary.*

a(n) = numerator(Sum_{m=1..n+1} IT(n,m)), n>=0, with IT(n,m):= A164658(n,m)/A164659(n,m) (coefficient triangle from the indefinite integral Integral_{x} T(n,x), n>=0, in lowest terms). A164658, revision 21, FORMULA: a(n,m) = numerator(b(n,m)), with int(T(n,x))= sum(b(n,m)*x^m,m=1..n+1), n>=0, where T(n,x) are Chebyshevs polynomials of the first kind. A164659 gives the denominators of the same coefficients. The primitive has zero constant coefficient. The row is summed over Finset.Icc 1 (m+1), with both endpoints included; its summand is the coefficient of degree j-1 in T(m,x), divided by j. Natural subtraction is used in j-1; the displayed division is rational.

**Definition 1.2 (The reduced numerator).**

$$\forall m \in \mathbb{N},\; a\left(m\right) = \operatorname{Rat.num}\left(rowSum\left(m\right)\right)$$

*Formalization.* `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.a` (`✓ std3`).

*Citation.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Commentary.*

a(n) = numerator(Sum_{m=1..n+1} IT(n,m)), n>=0, with IT(n,m):= A164658(n,m)/A164659(n,m) (coefficient triangle from the indefinite integral Integral_{x} T(n,x), n>=0, in lowest terms). The operation Rat.num is the reduced signed numerator with positive denominator.

**Definition 1.3 (The literal floor product).**

$$\forall n \in \mathbb{N},\; floorProduct\left(n\right) = \prod_{k \in \operatorname{Finset.Icc}\left(1, n\right)} (1 - 2 \cdot (\left\lfloor\frac{(k: \mathbb{Q})^{n}}{(n: \mathbb{Q})}\right\rfloor - \left\lfloor\frac{(k: \mathbb{Q})^{n} - 1}{(n: \mathbb{Q})}\right\rfloor))$$

*Formalization.* `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.floorProduct` (`✓ std3`).

*Citation.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Commentary.*

a(n+1) = Product_{k=1..n} ( 1-2*(floor(k^n/n)-floor((k^n -1)/n)) ) = (-1)^(A003557(n)) for n>0 (conjecture). - _Anthony Browne_, May 29 2016 The product is in the integers; exponentiation, subtraction and division inside each floor are rational operations. Finset.Icc includes one and n.

**Definition 1.4 (Browne's complete assertion).**

$$claim = \left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left((a\left(n + 1\right) = floorProduct\left(n\right)) \land (floorProduct\left(n\right) = ((-1: \mathbb{Z}))^{\operatorname{Nat.div}\left(n, \operatorname{UniqueFactorizationMonoid.radical}\left(n\right)\right)})\right)\right)$$

*Formalization.* `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.claim` (`✓ std3`).

*Citation.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Commentary.*

a(n+1) = Product_{k=1..n} ( 1-2*(floor(k^n/n)-floor((k^n -1)/n)) ) = (-1)^(A003557(n)) for n>0 (conjecture). - _Anthony Browne_, May 29 2016 The natural n satisfies 0<n. A003557(n) is n divided by its radical, with radical(1)=1. Both equalities are asserted, including n=1.

**Theorem 1.5 (The all-index identity).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left((a\left(n + 1\right) = floorProduct\left(n\right)) \land (floorProduct\left(n\right) = ((-1: \mathbb{Z}))^{\operatorname{Nat.div}\left(n, \operatorname{UniqueFactorizationMonoid.radical}\left(n\right)\right)})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.result` (`✓ std3`). ∎

*Resolves.* `Problems/b164660-chebfloor` (proved) by `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"b164660-chebfloor","declaration_gid":"D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Commentary.*

The floor difference is the indicator that n divides k to the power n. This is equivalent to the radical of n dividing k, so the product is minus one raised to the number n/radical(n) of positive multiples. That number is even exactly when four divides n. The polynomial T(n+2)/(2(n+2))-T(n)/(2n) has derivative T(n+1); its values at zero and one evaluate the rational row sum. Its reduced numerator is one when four divides n and minus one otherwise, giving the same sign for every positive n.

## References

- Truth anchor: `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.a`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.claim`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.floorProduct`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.result`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct.rowSum`
