# Failure above index two and refutation

## Abstract

Exact complete monotonicity classification of consecutive signed derivative ratios.

**Theorem 1.1 (Failure on every right half-line).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C.-F. Wei and B.-N. Guo (2014). *Complete monotonicity of functions connected with the exponential function and derivatives*. DOI: [10.1155/2014/851213](https://doi.org/10.1155/2014/851213). URL: <https://doi.org/10.1155/2014/851213>.

*Commentary.*

For every i at least three and every real T, there is t greater than both T and zero and an order k for which both signed ratio derivatives are negative. The second coefficient 2 times 3^i minus 4^i is negative. Its extracted limit is therefore eventually negative, while the sampling points tend to infinity. The two ratio families agree on a neighborhood of each positive sampling point.

**Theorem 1.2 (Refutation of the universal assertion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/wei-guo-2014-exponential-derivative-ratio-complete-monotonicity` (refuted) by `D5/S3/Analytic/ExpRatioCM/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wei-guo-2014-exponential-derivative-ratio-complete-monotonicity","declaration_gid":"D5/S3/Analytic/ExpRatioCM/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C.-F. Wei and B.-N. Guo (2014). *Complete monotonicity of functions connected with the exponential function and derivatives*. DOI: [10.1155/2014/851213](https://doi.org/10.1155/2014/851213). URL: <https://doi.org/10.1155/2014/851213>.

*Commentary.*

The universal assertion about both ratio families is false. Its specialization to index three contradicts both negative alternating derivatives supplied at a positive point by Result.failure_on_every_tail. Positive.cm_of_le_two independently proves the low-index positive cases.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.result`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Extraction](Extraction.md)
