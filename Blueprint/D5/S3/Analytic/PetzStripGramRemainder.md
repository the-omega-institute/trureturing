# The exponential deficit Gram and its logistic remainder

## Abstract

The exact Gram of exponential deficits on the two Petz strip boundaries dominates the logistic Gram of the boundary jump.

**Definition 1.1 (Logistic Fourier kernel).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.logistic`

*Formalization.* `D5/S3/Analytic/PetzStripGramRemainder.logistic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero the kernel is one. At frequency x away from zero it is (x/2) divided by sinh(x/2).

**Definition 1.2 (Exponential deficit).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.deficit`

*Formalization.* `D5/S3/Analytic/PetzStripGramRemainder.deficit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At real frequency x and complex argument z the deficit is 1 minus exp(x z).

**Definition 1.3 (Closed strip Gram entry).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.stripGram`

*Formalization.* `D5/S3/Analytic/PetzStripGramRemainder.stripGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For frequencies x and y, the entry is minus (x+y)/2 plus exp(x/2) exp(y/2) times the logistic kernel at y-x, minus (y-x)/2 times coth((y-x)/2). The last factor takes the value one when x=y.

**Definition 1.4 (Weighted conjugate product).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.weightedPair`

*Formalization.* `D5/S3/Analytic/PetzStripGramRemainder.weightedPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the vertical line with real part a, multiply the conjugate of the first deficit by the second deficit and by the weight at the imaginary coordinate.

**Theorem 1.5 (Exact weighted strip Gram).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.weighted_strip_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzStripGramRemainder.weighted_strip_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

The weighted conjugate products on the lines with real parts zero and one half are integrable, and the sum of their whole-line integrals is the closed strip Gram entry. The weights are pi/(cosh(2 pi t) - 1) on the lower line and pi/(cosh(2 pi t) + 1) on the upper line. At x=y the entry is exp(x) - 1 - x.

On the lower line, the two diagonal deficits dominate the absolute value of the mixed product. Reflecting the imaginary coordinate then reduces the integral to three compensated cosine modes. On the upper line each individual Fourier mode is integrable. The logistic Gram factorization supplies its real transform and fixes the unit mass. The finite-overlap strip identity evaluates the cosine coefficient using the coth integral on the lower line. Summing the two boundary contributions gives the closed formula, including zero and coincident frequencies.

**Definition 1.6 (Logistic remainder entry).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.remainder`

*Formalization.* `D5/S3/Analytic/PetzStripGramRemainder.remainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the logistic kernel at y-x multiplied by the two real jump coefficients 1-exp(x/2) and 1-exp(y/2) from the closed strip Gram entry.

**Theorem 1.7 (Nonnegative remainder for complex amplitudes).**

Lean statement: `D5/S3/Analytic/PetzStripGramRemainder.remainder_quadratic_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzStripGramRemainder.remainder_quadratic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For any finite family of real frequencies and complex amplitudes, the real part of the quadratic form of the closed logistic remainder is nonnegative. The family may contain coincident or zero frequencies.

Apply the bounded analytic strip comparison to the finite linear combination of the deficits. The boundary energies give the closed strip Gram, while the difference of the two boundary values gives the logistic energy of the jump coefficients.

## References

- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.deficit`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.logistic`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.remainder`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.remainder_quadratic_nonneg`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.stripGram`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.weightedPair`
- Truth anchor: `D5/S3/Analytic/PetzStripGramRemainder.weighted_strip_gram`
- Dependency: [D5/S3/Analytic/PetzLogisticEvaluation](PetzLogisticEvaluation.md)
- Dependency: [D5/S3/Analytic/PetzLogisticMidline](PetzLogisticMidline.md)
