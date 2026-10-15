# Hanna's bilateral Laurent rows

## Abstract

The nonpositive Laurent coefficients in A391810 have zero full row sum.

**Definition 1.1 (Laurent monomials).**

$$\forall k \in \mathbb{Z},\; \operatorname{z}\left(k\right) = \operatorname{single}\left(k, 1\right)$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.z` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The monomial x to the integer power k has coefficient one at k and zero elsewhere.

**Definition 1.2 (The original rational summand).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \operatorname{summand}\left(n, k\right) = \operatorname{z}\left(k\right) \cdot \left(1 - \operatorname{z}\left(k\right)\right)^{n + k}$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.summand` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

Work in rational Laurent series expanded at zero. Integer powers use the field inverse for negative exponents. For positive n the zero-index term vanishes.

**Theorem 1.3 (The order of a nonzero-index summand).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; k \ne 0 \Rightarrow \operatorname{order}\left(\operatorname{summand}\left(n, k\right)\right) = k + \left(n + k\right) \cdot \operatorname{min}\left(0, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.summand_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The order of 1 minus x to the k is the minimum of zero and k. Orders add under multiplication and multiply by the integer exponent under powers of a nonzero series.

**Theorem 1.4 (A common lower support bound).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall k \in \mathbb{Z},\; \forall d \in \mathbb{Z},\; \operatorname{coeff}\left(\operatorname{summand}\left(n, k\right), d\right) \ne 0 \Rightarrow -\left(n + 1\right)^{2} \le d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.summand_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

Completing the square in the negative-index order gives a uniform lower bound. This makes the union of supports well founded.

**Theorem 1.5 (Finite contributions to each coefficient).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall d \in \mathbb{Z},\; \operatorname{Finite}\left(\{k \in \mathbb{Z} \Vert \operatorname{coeff}\left(\operatorname{summand}\left(n, k\right), d\right) \ne 0\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.coefficient_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

For each fixed exponent, only a bounded integer interval of outer indices can have a nonzero coefficient. Both tails eventually have order above that exponent.

**Definition 1.6 (The formally summable bilateral family).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall k \in \mathbb{Z},\; \operatorname{family}\left(n, k\right) = \operatorname{summand}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.family` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The family bundles the original summands with their common lower support bound and finite contributions at every coefficient. Its formal sum is therefore a genuine Laurent series.

**Definition 1.7 (The original bilateral Laurent sum).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{series}\left(n\right) = \operatorname{hsum}\left(\operatorname{family}\left(n\right)\right)$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.series` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The formal Hahn sum adds each coefficient using its finitely many contributing terms. It retains all positive and negative integer outer indices.

**Definition 1.8 (The finite inverse-variable row polynomial).**

$$\forall n \in \mathbb{N},\; \operatorname{rowPolynomial}\left(n\right) = -1 + \sum_{0 \leq j < n} \operatorname{X}\left(\right)^{j + 1} \cdot \left(1 - \operatorname{X}\left(\right)^{j + 1}\right)^{n - \left(j + 1\right)}$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.rowPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

Here x denotes the polynomial variable, corresponding to the inverse of the original Laurent variable. The indices minus one through minus n give these polynomial summands. The index minus n minus one supplies constant minus one; all remaining outer indices have only positive Laurent powers.

**Theorem 1.9 (Exact integer identification of every nonpositive coefficient).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall m \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{series}\left(n\right), -m\right) = \operatorname{rationalCast}\left(\operatorname{coeff}\left(\operatorname{rowPolynomial}\left(n\right), m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

This identity proves that the finite polynomial describes the full nonpositive truncation, including its constant term, and that every such rational coefficient comes from an integer.

**Definition 1.10 (The published inclusive row bound).**

$$\forall n \in \mathbb{N},\; \operatorname{rowBound}\left(n\right) = \left\lfloor\frac{n + 1}{2}\right\rfloor^{2}$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.rowBound` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The last coefficient index is floor((n+1)/2) squared.

**Theorem 1.11 (The exact full-row support bound).**

$$\forall n \in \mathbb{N},\; \operatorname{natDegree}\left(\operatorname{rowPolynomial}\left(n\right)\right) \le \operatorname{rowBound}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.row_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

Expand each polynomial summand by the binomial theorem. Its terms below the highest term have exponent at most the row bound. If n is even, the highest terms cancel under reflection of the outer index. If n is odd, their degrees already satisfy the bound.

**Definition 1.12 (Integer triangle coefficients).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{rowEntry}\left(n, m\right) = \operatorname{coeff}\left(\operatorname{rowPolynomial}\left(n\right), m\right)$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentRowSums.rowEntry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The coefficient bridge identifies this integer with T(n,m) in the original Laurent definition.

**Theorem 1.13 (The universal zero row sum with its original-series support).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\sum_{0 \leq m < \operatorname{rowBound}\left(n\right) + 1} \operatorname{rowEntry}\left(n, m\right) = 0 \land \left(\sum_{0 \leq m < \operatorname{rowBound}\left(n\right) + 1} \operatorname{coeff}\left(\operatorname{series}\left(n\right), -m\right) = 0 \land \left(\forall m \in \mathbb{N},\; \operatorname{rowBound}\left(n\right) < m \Rightarrow \operatorname{coeff}\left(\operatorname{series}\left(n\right), -m\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentRowSums.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391810-full-laurent-row-sums` (proved) by `D5/S3/ArithSums/HannaLaurentRowSums.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391810-full-laurent-row-sums","declaration_gid":"D5/S3/ArithSums/HannaLaurentRowSums.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

Evaluate only the finite inverse-variable polynomial at one. Every outer term vanishes except its final term, which equals one and cancels the constant minus one. The degree bound makes this evaluation the full inclusive row sum. The coefficient bridge transfers both the zero sum and the full support bound to the original bilateral Laurent series.

## References

- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.coefficient_finite`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.family`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.result`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.rowBound`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.rowEntry`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.rowPolynomial`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.row_degree`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.series`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.summand`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.summand_lower_bound`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.summand_order`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentRowSums.z`
