# Failure above index two and refutation

## Abstract

Exact complete monotonicity classification of consecutive signed derivative ratios.

**Theorem 1.1 (Failure on every right half-line).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every i at least three and every real T, there is t greater than both T and zero and an order k for which both signed ratio derivatives are negative. The second coefficient 2 times 3^i minus 4^i is negative. Its extracted limit is therefore eventually negative, while the sampling points tend to infinity. The two ratio families agree on a neighborhood of each positive sampling point.

**Theorem 1.2 (Indices at least three).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both ratio families fail complete monotonicity whenever the index is at least three.

**Theorem 1.3 (Classification of the first family).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.classification`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first ratio is completely monotone on the positive half-line if and only if its index is at most two. The low-index closed forms give sufficiency; the extracted negative coefficient gives necessity.

**Theorem 1.4 (Classification of the second family).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.classificationG`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.classificationG` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second ratio has exactly the same completely monotone indices: zero, one, and two.

**Theorem 1.5 (Refutation of the universal assertion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal assertion about both ratio families is false. Its specialization to index three contradicts the exact classification.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.classification`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.classificationG`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.result`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Extraction](Extraction.md)
- Dependency: [D5/S3/Analytic/ExpRatioCM/Positive](Positive.md)
