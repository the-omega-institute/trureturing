# Kurkov's universal convolution-row recursion

## Abstract

Kurkov's shifted array gives every positive convolution-row polynomial over a commutative semiring.

The coefficient semiring K is arbitrary. Natural indices include zero, but the sequence contributes only at positive indices. PowerSeries.X is the series variable, and Polynomial.X is the polynomial variable. The entry OEIS A340991 is unpaginated; the quotations below are its FORMULA lines in revision 24.

**Definition 1.1 (The source series).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (a: \mathbb{N} \to K), \operatorname{sourceSeries}\left(a\right) = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} j: \mathbb{N} \mapsto \operatorname{if} j = 0 \operatorname{then} 0 \operatorname{else} a\left(j\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.sourceSeries` (`✓ std3`).

*Citation.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

T(n,k) = [x^n] (Sum_{j>=1} prime(j)*x^j)^k. The coefficient sequence prime(j) is replaced by an arbitrary a. PowerSeries.mk assigns coefficient zero at j=0 and coefficient a(j) at every positive j.

**Definition 1.2 (Equality with the source series).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (a: \mathbb{N} \to K), \forall (A: \operatorname{PowerSeries}\left(K\right)), \operatorname{IsSourceSeries}\left(a, A\right) \Leftrightarrow A = \operatorname{sourceSeries}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.IsSourceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

A is the source series exactly when it equals sourceSeries(a).

**Definition 1.3 (The convolution coefficient triangle).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (A: \operatorname{PowerSeries}\left(K\right)), \forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{T}\left(A, n, r\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(n, A^{r}\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.T` (`✓ std3`).

*Citation.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

T(n,k) = [x^n] (Sum_{j>=1} prime(j)*x^j)^k. The degree n coefficient of A raised to r is the triangle entry T(A,n,r). The zeroth power is one.

**Definition 1.4 (The finite row polynomial).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (A: \operatorname{PowerSeries}\left(K\right)), \forall (n: \mathbb{N}), \operatorname{rowPolynomial}\left(A, n\right) = \sum_{r \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{Polynomial}.\operatorname{C}\left(\operatorname{T}\left(A, n, r\right)\right) \cdot \operatorname{Polynomial}.\operatorname{X}^{r})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.rowPolynomial` (`✓ std3`).

*Citation.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

The row polynomial has coefficient T(A,n,r) at power r for r=0,...,n. The range n+1 includes both endpoints.

**Definition 1.5 (Kurkov's shifted polynomial array).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (a: \mathbb{N} \to K), \begin{aligned}\forall (k: \mathbb{N}), \operatorname{kurkovR}\left(a, 0, k\right) = 0\\\operatorname{kurkovR}\left(a, 1, 0\right) = 0\\\forall (k: \mathbb{N}), \operatorname{kurkovR}\left(a, 1, k + 1\right) = \operatorname{Polynomial}.\operatorname{C}\left(a\left(k + 1\right)\right)\\\forall (n: \mathbb{N}), \operatorname{kurkovR}\left(a, n + 2, 0\right) = 0\\\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{kurkovR}\left(a, n + 2, k + 1\right) = \operatorname{kurkovR}\left(a, n + 1, k + 2\right) + \operatorname{Polynomial}.\operatorname{X} \cdot \operatorname{Polynomial}.\operatorname{C}\left(a\left(k + 1\right)\right) \cdot \operatorname{kurkovR}\left(a, n + 1, 1\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.kurkovR` (`✓ std3`).

*Citation.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = prime(k) for k > 0. The same recursion seems to work for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025 Positive columns start with C(a(k)). Row zero and column zero are zero. In the successor equation n and k range over all natural numbers. Commutativity allows the product order X*C(a(k+1))*kurkovR(a,n+1,1).

**Definition 1.6 (The universal row identity).**

$$\operatorname{claim} \Leftrightarrow \forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (a: \mathbb{N} \to K), \exists (A: \operatorname{PowerSeries}\left(K\right)), (\operatorname{IsSourceSeries}\left(a, A\right)) \land (\forall (n: \mathbb{N}), 1 \le n \Rightarrow \operatorname{rowPolynomial}\left(A, n\right) = \operatorname{Polynomial}.\operatorname{X} \cdot \operatorname{kurkovR}\left(a, n, 1\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.claim` (`✓ std3`).

*Citation.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = prime(k) for k > 0. The same recursion seems to work for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025 For every commutative semiring and sequence, there exists its zero-constant source series, and every row with 1<=n equals Polynomial.X times column one of kurkovR. Row zero is outside the asserted identity; a(0) does not occur.

**Theorem 1.7 (The universal convolution-row recursion).**

$$\forall (K: \operatorname{Type}), [\operatorname{CommSemiring}\left(K\right)] \forall (a: \mathbb{N} \to K), \exists (A: \operatorname{PowerSeries}\left(K\right)), (\operatorname{IsSourceSeries}\left(a, A\right)) \land (\forall (n: \mathbb{N}), 1 \le n \Rightarrow \operatorname{rowPolynomial}\left(A, n\right) = \operatorname{Polynomial}.\operatorname{X} \cdot \operatorname{kurkovR}\left(a, n, 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alois P. Heinz; Mikhail Kurkov (2025). *OEIS A340991: self-convolution triangle and Kurkov's row recursion*. URL: <https://oeis.org/A340991>.

*Commentary.*

Splitting the coefficient tail into its constant term and PowerSeries.X times the next tail reproduces the two summands of kurkovR. Induction identifies each positive array column coefficient with a coefficient of a source-series power times that tail. Coefficients below the power vanish, giving the finite row polynomial. No positivity, nonzero coefficient, division, or characteristic assumption is required.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.T`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.kurkovR`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.rowPolynomial`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.sourceSeries`
- Dependency: [D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries](RecursiveBoundaryRowSeries.md)
