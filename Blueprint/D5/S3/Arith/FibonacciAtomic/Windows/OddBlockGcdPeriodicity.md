# Joint Odd-Length Gibonacci GCD Periodicity

## Abstract

Both infinite-shift Gibonacci window gcds are periodic on positive odd lengths for every integer seed pair.

All seed values a,b,c and divisors d are integers. Indices n,t,k,j and periods P are natural numbers, including zero. G(a,b,n), U(a,b,t,k), W(a,b,t,k), A(a,b,k) and B(a,b,k) denote the five definitions below. The natural range(k) is the set of indices i with 0 <= i < k; in particular range(0) is empty.

**Definition 1.1 (The exact seeded recurrence).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall n \in \mathbb{N},\; \operatorname{G}\left(a, b, n\right) = \operatorname{fst}\left(\operatorname{iterate}\left(step, n, (a, b)\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.g` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

The map step sends (x,y) to (y,x+y). The first coordinate of its n-fold iterate from (a,b) is G(a,b,n). Its initial values are a,b and its recurrence is G(n+2)=G(n)+G(n+1). The result also identifies it with every integer sequence having those initial values and recurrence.

**Definition 1.2 (Actual linear windows).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{U}\left(a, b, t, k\right) = \sum_{i \in \operatorname{range}\left(k\right)} \operatorname{G}\left(a, b, t + i + 1\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.sumWindow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

U is the sum of G(t+1) through G(t+k). Every natural shift t is retained, and the length-zero window is zero.

**Definition 1.3 (Actual square windows).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{W}\left(a, b, t, k\right) = \sum_{i \in \operatorname{range}\left(k\right)} (\operatorname{G}\left(a, b, t + i + 1\right))^{2}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.squareWindow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

W sums the squares of exactly the same terms. It is an integer sum, with no restriction on the signs or common factors of the initial values.

**Definition 1.4 (The normalized linear gcd).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{N},\; \operatorname{A}\left(a, b, k\right) = \operatorname{gcd}\left(\lvert \operatorname{U}\left(a, b, 0, k\right) \rvert, \lvert \operatorname{U}\left(a, b, 1, k\right) \rvert\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.sumGcd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

A is a natural gcd of the first two actual windows. The result proves that an arbitrary integer d divides A exactly when it divides U at every natural shift, so this finite expression represents the source's infinite gcd.

**Definition 1.5 (The normalized square gcd).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{N},\; \operatorname{B}\left(a, b, k\right) = \operatorname{gcd}\left(\operatorname{gcd}\left(\lvert \operatorname{W}\left(a, b, 0, k\right) \rvert, \lvert \operatorname{W}\left(a, b, 1, k\right) \rvert\right), \lvert \operatorname{W}\left(a, b, 2, k\right) \rvert\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.squareGcd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

B is the nested natural gcd of the first three square windows. Its universal integer-divisor specification is proved for all shifts, including d=0. Absolute values only normalize the gcd; they do not restrict the source sequence.

**Theorem 1.6 (The whole odd-length question).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; ((\operatorname{G}\left(a, b, 0\right) = a) \land \left((\operatorname{G}\left(a, b, 1\right) = b) \land (\forall n \in \mathbb{N},\; \operatorname{G}\left(a, b, n + 2\right) = \operatorname{G}\left(a, b, n\right) + \operatorname{G}\left(a, b, n + 1\right))\right)) \land \left((\forall u \in \mathbb{N} \to \mathbb{Z},\; (\operatorname{u}\left(0\right) = a) \Rightarrow ((\operatorname{u}\left(1\right) = b) \Rightarrow ((\forall n \in \mathbb{N},\; \operatorname{u}\left(n + 2\right) = \operatorname{u}\left(n\right) + \operatorname{u}\left(n + 1\right)) \Rightarrow (\forall n \in \mathbb{N},\; \operatorname{u}\left(n\right) = \operatorname{G}\left(a, b, n\right))))) \land \left((\forall k \in \mathbb{N},\; \forall d \in \mathbb{Z},\; ((d \mid \operatorname{A}\left(a, b, k\right)) \Leftrightarrow (\forall t \in \mathbb{N},\; d \mid \operatorname{U}\left(a, b, t, k\right))) \land ((d \mid \operatorname{B}\left(a, b, k\right)) \Leftrightarrow (\forall t \in \mathbb{N},\; d \mid \operatorname{W}\left(a, b, t, k\right)))) \land \left((\forall c \in \mathbb{Z},\; \forall k \in \mathbb{N},\; (\operatorname{A}\left(c \cdot a, c \cdot b, k\right) = \lvert c \rvert \cdot \operatorname{A}\left(a, b, k\right)) \land (\operatorname{B}\left(c \cdot a, c \cdot b, k\right) = (\lvert c \rvert)^{2} \cdot \operatorname{B}\left(a, b, k\right))) \land \left((\exists P \in \mathbb{N},\; (0 < P) \land (\forall j \in \mathbb{N},\; (\operatorname{A}\left(a, b, 2 \cdot (j + P) + 1\right) = \operatorname{A}\left(a, b, 2 \cdot j + 1\right)) \land (\operatorname{B}\left(a, b, 2 \cdot (j + P) + 1\right) = \operatorname{B}\left(a, b, 2 \cdot j + 1\right)))) \land (((a = 0) \land (b = 0)) \Rightarrow (\forall k \in \mathbb{N},\; (\operatorname{A}\left(a, b, k\right) = 0) \land (\operatorname{B}\left(a, b, k\right) = 0)))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/mbirika-spilker-gibonacci-odd-block-gcd-periodicity` (proved) by `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mbirika-spilker-gibonacci-odd-block-gcd-periodicity","declaration_gid":"D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* aBa Mbirika, Jürgen Spilker (2023). *GCD of sums of k consecutive squares of generalized Fibonacci numbers*. URL: <https://arxiv.org/abs/2204.12626v2>.

*Commentary.*

For every integer pair a,b, both odd subsequences have one common positive period P from j=0, corresponding to length k=1. The theorem includes the initial values, recurrence uniqueness, both infinite-shift divisor specifications, and scaling by every signed integer c. Thus nonprimitive seeds require no additional hypothesis. For (0,0), both gcds are identically zero under the normalized convention; this extension is separate from the source's relatively-prime seed convention. No least-period assertion or even-length periodicity assertion is made.

To see why the finite gcds retain all shifts, U obeys an order-two recurrence in t, while W obeys W(t+3)=2W(t+2)+2W(t+1)-W(t). Divisibility therefore propagates from the first two or three windows, respectively. Direct telescoping gives U(t,k)=G(t+k+2)-G(t+2) and W(t,k)=G(t+k)G(t+k+1)-G(t)G(t+1).

Write mu=b^2-ab-a^2 and Q(x,y)=y^2-xy-x^2. The step reverses Q, so Q(G(n),G(n+1))=(-1)^n mu. At odd k, A and B both divide M=2|mu|. For the linear family this follows by applying Q to the endpoint differences. For the square family, W(2,k)-3W(1,k)+W(0,k)=2mu. The golden integer norm of (a,b) is -mu; its zero-norm characterization shows that mu=0 occurs exactly at the zero pair.

For a nonzero pair, M is positive. The existing complete-state return for step on (ZMod M)^2 supplies R=(M^2)!, a positive return time. Integer reduction commutes with every step. Consequently the two telescoping endpoints are unchanged modulo M after increasing k by 2R. Both old and new odd-length gcds divide M; their universal divisor specifications give divisibility in both directions. This yields the common odd-index period P=R. The factorial is a symbolic existence witness and is not asserted to be minimal.

Guyer-Mbirika, arXiv:2104.12262v2, Theorems 3.1 and 3.5, supplies the linear finite-gcd and scaling formulas. Mbirika-Spilker, arXiv:2204.12626v2, Theorems 3.4, 3.6 and 4.8, supplies the square finite formula, square scaling and odd fixed cap. Chen-Pan, Greatest Common Divisors of Shifted Horadam Sequences, JIS 23, Article 20.5.8, already proves the linear periodicity corollary and uses the finite modular-state method. With their parameters p=1,q=-1,s=-b,t=-(a+b),phi(j)=2j+2, their shifted pair is the linear gcd at length 2j+1. The joint conclusion here connects that method to the genuine infinite square-window gcd. Equivalent whole coverage in Spilker's 2016 generalized chapter remains unverified; the bounded source comparison does not establish first-publication priority.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.g`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.squareGcd`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.squareWindow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.sumGcd`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.sumWindow`
- Dependency: [D5/S0/Carrier/Norm](../../../../S0/Carrier/Norm.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](../GraftAffineClosure.md)
