# The logarithmic-polynomial recursion of OEIS A263634

## Abstract

Kurkov's recursion gives every logarithmic polynomial in every positive row.

The coefficient algebra is MvPolynomial ℕ ℚ. Its indeterminates are indexed by natural numbers; the variable with index zero does not occur in any positive-column recursion. PowerSeries.logOf is the formal logarithm of a series with constant coefficient one. All series and derivatives here are formal; no analytic convergence is assumed.

**Definition 1.1 (The source exponential series).**

$$sourceSeries = \operatorname{PowerSeries}.\operatorname{mk}\left(fun (i: \mathbb{N}) \mapsto if i = 0 then 1 else \operatorname{MvPolynomial}.\operatorname{C}\left(\operatorname{Inv}.\operatorname{inv}\left((\operatorname{Nat}.\operatorname{factorial}\left(i\right): \mathbb{Q})\right)\right) \cdot \operatorname{MvPolynomial}.\operatorname{X}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.sourceSeries` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A263634: the logarithmic-polynomial recursion*. URL: <https://oeis.org/A263634>.

*Commentary.*

OEIS A263634, revision 166, unpaginated FORMULA field: G.f.: Log(1 + Sum_{i >= 1} x_i*t^i/i!) =  Sum_{n >= 1} L_n(x_1, x_2, ...)*t^n/n!. [Comtet, p. 140, Eq. [5a]. - corrected by _Tom Copeland_, Sep 08 2016] The coefficient at zero is one; at positive i it is MvPolynomial.C of the rational inverse of i factorial, multiplied by MvPolynomial.X i. Sorting monomials affects only the printed coefficient list.

**Definition 1.2 (The logarithmic-polynomial family).**

$$\forall L \in \mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{Q}\right),\; (\operatorname{IsSourceFamily}\left(L\right)) \Leftrightarrow ((L\left(0\right) = 0) \land (\operatorname{PowerSeries}.\operatorname{logOf}\left(sourceSeries\right) = \operatorname{PowerSeries}.\operatorname{mk}\left(fun (n: \mathbb{N}) \mapsto \operatorname{MvPolynomial}.\operatorname{C}\left(\operatorname{Inv}.\operatorname{inv}\left((\operatorname{Nat}.\operatorname{factorial}\left(n\right): \mathbb{Q})\right)\right) \cdot L\left(n\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.IsSourceFamily` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A263634: the logarithmic-polynomial recursion*. URL: <https://oeis.org/A263634>.

*Commentary.*

OEIS A263634, revision 166, unpaginated FORMULA field: G.f.: Log(1 + Sum_{i >= 1} x_i*t^i/i!) =  Sum_{n >= 1} L_n(x_1, x_2, ...)*t^n/n!. [Comtet, p. 140, Eq. [5a]. - corrected by _Tom Copeland_, Sep 08 2016] The auxiliary value L 0 is zero. Every positive coefficient has the factorial normalization printed in the source.

**Definition 1.3 (The recursive array).**

$$\begin{aligned}\forall k \in \mathbb{N},\; \operatorname{R}\left(0, k\right) = 0\\\forall k \in \mathbb{N},\; \operatorname{R}\left(1, k\right) = \operatorname{MvPolynomial}.\operatorname{X}\left(k\right)\\\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{R}\left(m + 2, k\right) = \operatorname{R}\left(m + 1, k + 1\right) - \sum_{r: \operatorname{Fin}\left(m + 1\right)}(\operatorname{MvPolynomial}.\operatorname{C}\left((\operatorname{Nat}.\operatorname{choose}\left(m, \operatorname{val}\left(r\right)\right): \mathbb{Q})\right) \cdot \operatorname{R}\left(\operatorname{val}\left(r\right) + 1, k\right) \cdot \operatorname{R}\left(m - \operatorname{val}\left(r\right) + 1, 1\right))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.R` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A263634: the logarithmic-polynomial recursion*. URL: <https://oeis.org/A263634>.

*Commentary.*

OEIS A263634, revision 166, unpaginated FORMULA field: Conjecture: row polynomials are R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} binomial(n-2,j-1)*R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = x_k for k > 0. - _Mikhail Kurkov_, Mar 30 2025 In the last equation n = m + 2 and j = r.val + 1. Thus r ranges over Fin (m + 1), the binomial weight is m.choose r.val, and the other row is m - r.val + 1. This subtraction is natural subtraction, with r.val ≤ m. Row zero is extended by zero; column zero is outside the assertion.

**Definition 1.4 (Kurkov's complete conjecture).**

$$(claim) \Leftrightarrow ((\exists L \in \mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{Q}\right),\; \operatorname{IsSourceFamily}\left(L\right)) \land (\forall L \in \mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{Q}\right),\; (\operatorname{IsSourceFamily}\left(L\right)) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{R}\left(n, 1\right) = L\left(n\right)))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.claim` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A263634: the logarithmic-polynomial recursion*. URL: <https://oeis.org/A263634>.

*Commentary.*

OEIS A263634, revision 166, unpaginated FORMULA field: Conjecture: row polynomials are R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} binomial(n-2,j-1)*R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = x_k for k > 0. - _Mikhail Kurkov_, Mar 30 2025 The logarithmic-polynomial family is specified by: G.f.: Log(1 + Sum_{i >= 1} x_i*t^i/i!) =  Sum_{n >= 1} L_n(x_1, x_2, ...)*t^n/n!. [Comtet, p. 140, Eq. [5a]. - corrected by _Tom Copeland_, Sep 08 2016] The assertion includes existence and identifies every family with that generating series at every positive row. The variables remain algebraically independent.

**Theorem 1.5 (The recursion gives the logarithmic polynomials).**

$$(\exists L \in \mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{Q}\right),\; \operatorname{IsSourceFamily}\left(L\right)) \land (\forall L \in \mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{Q}\right),\; (\operatorname{IsSourceFamily}\left(L\right)) \Rightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{R}\left(n, 1\right) = L\left(n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2025). *OEIS A263634: the logarithmic-polynomial recursion*. URL: <https://oeis.org/A263634>.

*Commentary.*

Put Q k = ((PowerSeries.derivative)^[k] sourceSeries) * PowerSeries.invOfUnit sourceSeries 1 inside the proof. Differentiating its product with sourceSeries gives D(Q k) = Q (k + 1) - Q k * Q 1. The iterated product rule produces exactly the binomial convolution in R. Simultaneous induction over all positive columns identifies R (n + 1) k with the constant coefficient of D^[n](Q k). The formal logarithmic derivative then identifies the first column. Coefficient comparison proves the assertion for every source family, and also constructs such a family.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.IsSourceFamily`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.R`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.claim`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.result`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.sourceSeries`
- Dependency: [D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums](PositiveNewtonSums.md)
