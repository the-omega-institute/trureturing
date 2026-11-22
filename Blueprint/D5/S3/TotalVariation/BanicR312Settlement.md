# A bin-count reversal for cyclic multinomial dispersion

## Abstract

At four draws, a fourth bin increases cyclic multinomial dispersion.

**Definition 1.1 (Proposed monotonicities).**

$$[\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma(n + 1,N) \le \sigma(n,N)] \land [\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma(n,N) \le \sigma(n,N + 1)]$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.claim` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

The count vector has n bins and N draws with uniform bin probabilities. Its law is the sum of point masses of weight N! divided by the product of the count factorials, times n to the power −N. Vectors whose counts sum to a different total have weight zero. The cyclic variation D sums the absolute differences of consecutive counts, including the closing edge. The dispersion σ(n,N) is the square root of Var(D)/N. Each inequality ranges over natural n at least three and N at least one, as in the two questions in Remark 3.12.

**Theorem 1.2 (Refutation of the joint monotonicity claim).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/BanicR312Settlement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For each bin count, sum the integer multinomial weight times D to powers zero, one and two over the bounded count vectors. At (3,4) these sums are (81,312,1488) and at (4,4) they are (256,1120,5888). The zeroth sums give total probability one after division by n to the power N. The first and second sums give the corresponding moments under the same measure.

Subtracting the squared first moment from the second moment and dividing by N gives normalized variances 644/729 and 247/256, respectively. Taking the square root preserves the strict increase from three to four bins at four draws. This contradicts the bin-count clause of the conjunction.

## References

- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.claim`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.result`
