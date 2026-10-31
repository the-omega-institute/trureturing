# The first moment of Hanna's Laurent rows

## Abstract

The first weighted moment of every positive A391810 Laurent row is one.

Formula (3) in Paul D. Hanna's OEIS A391810, revision 39, states: (3) Sum_{k=0..floor((n+1)/2)^2} k * T(n,k) = 1 for n >= 1 (conjecture). This is the weighted assertion; the zero row sum in formula (2) is a separate assertion. The shared library note supplies the source locator and Laurent-series convention; its claim quotation concerns formula (2).

The original series is the formal expansion at zero of Sum_{j in Z} x^j*(1-x^j)^(n+j), with all integer outer indices and Laurent-field inverses for negative integer powers. T(n,k) is its signed coefficient of x^(-k), including k=0. The imported coefficient bridge identifies it with the integer rowEntry(n,k). The imported row bound is exactly floor((n+1)/2)^2 and the final index is included.

**Theorem 1.1 (The integer and literal Laurent weighted sums).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\sum_{0 \leq k \leq \left\lfloor\frac{n + 1}{2}\right\rfloor^{2}} k \cdot \operatorname{rowEntry}\left(n, k\right) = 1 \land \sum_{0 \leq k \leq \left\lfloor\frac{n + 1}{2}\right\rfloor^{2}} k \cdot \operatorname{coeff}\left(\operatorname{series}\left(n\right), -k\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentFirstMoment.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391810-laurent-first-moment` (proved) by `D5/S3/ArithSums/HannaLaurentFirstMoment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391810-laurent-first-moment","declaration_gid":"D5/S3/ArithSums/HannaLaurentFirstMoment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The first equality is in the integers; the second is in the rationals, using the literal Laurent coefficients. Both hold for every natural n with 0<n. The coefficient bridge retains the constant term and every nonpositive coefficient, while the existing degree bound identifies the displayed finite sum with the full row moment.

Differentiate only the finite inverse-variable rowPolynomial. For n=1 its derivative is one. For n>=2, evaluation at one annihilates every differentiated summand except the last two, whose values are n and -(n-1). Their sum is one. The polynomial derivative coefficient identity gives the integer weighted sum, and the exact coefficient bridge transfers it to the original bilateral series. No evaluation of the bilateral series at one is used.

This is an application of the existing coefficient and support theorems and polynomial differentiation. Its mathematical scope is the published formula (3) with its original range and arithmetic. Global priority and global prior solvedness remain outside the theorem.

## References

- Truth anchor: `D5/S3/ArithSums/HannaLaurentFirstMoment.result`
- Dependency: [D5/S3/ArithSums/HannaLaurentRowSums](HannaLaurentRowSums.md)
