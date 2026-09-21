# Localization for the Powered-Sum Ratio

## Abstract

Maximizers of the ratio of powered binomial sums have a common limiting slope.

**Definition 1.1 (The actual ratio of powered sums).**

Lean statement: `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.poweredRatio`

*Formalization.* `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.poweredRatio` (`✓ std3`).

*Citation.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

poweredRatio(a,l,m,r) = sum(i=0..r, (choose(m,i) a^i)^l) / sum(i=0..r, (choose(r,i) a^i)^l). Both products, including their weights, are raised to l. This is the sequence in equation (1.4) of the source.

**Theorem 1.2 (Every maximizing choice has slope a divided by one plus two a).**

Lean statement: `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.actual_maximizer_slope`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.actual_maximizer_slope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

For every fixed positive real a and positive natural l, any sequence r(m)<=m maximizing poweredRatio over every integer 0<=j<=m has r(m)/m tending to a/(1+2a). A power-mean denominator bound contributes a polynomial factor, which the existing exponential separation absorbs. Ties are allowed, with no uniqueness or unimodality premise. The slope alone does not supply the exact maximum prefactor or any exact peak assertion.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.actual_maximizer_slope`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.poweredRatio`
- Dependency: [D5/S3/AnalyticClosure/BinomialMaximumLocalization](BinomialMaximumLocalization.md)
