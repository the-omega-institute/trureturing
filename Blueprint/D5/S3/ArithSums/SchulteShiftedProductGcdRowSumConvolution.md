# OEIS A347293 row-sum convolution

## Abstract

Schulte's shifted-product gcd row sum equals a divisor convolution of squares and squared totients.

**Definition 1.1 (The shifted-product gcd row sum).**

$$\forall n \in \mathrm{Nat},\; \operatorname{rowSum}\left(n\right) = \sum_{x \in \operatorname{range}\left(n\right)} (\sum_{y \in \operatorname{range}\left(n\right)} \operatorname{gcd}\left(1 + x \cdot y, n\right))$$

*Formalization.* `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.rowSum` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A347293, shifted-product gcd triangle and row-sum convolution*. URL: <https://oeis.org/A347293>.

*Commentary.*

The two range sums run over x and y from zero through n minus one. They are the OEIS triangle's row sum after the index changes x=i-1 and y=k-1.

**Theorem 1.2 (The square and squared-totient convolution).**

$$\forall n \in \mathrm{Nat},\; (n > 0) \Rightarrow (\operatorname{rowSum}\left(n\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} d^{2} \cdot \operatorname{totient}\left(n / d\right)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347293-schulte-shifted-product-gcd-row-sum-convolution` (proved) by `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347293-schulte-shifted-product-gcd-row-sum-convolution","declaration_gid":"D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2022). *OEIS A347293, shifted-product gcd triangle and row-sum convolution*. URL: <https://oeis.org/A347293>.

*Commentary.*

For each divisor d of n, reduction modulo d identifies the pairs with d dividing 1+xy with a unit and its unique negative inverse. There are totient(d) residue pairs and each has (n/d)^2 lifts. Expanding each gcd by the totient divisor sum and reindexing complementary divisors gives the displayed convolution.

## References

- Truth anchor: `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.result`
- Truth anchor: `D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution.rowSum`
