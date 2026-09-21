# Localization for the Simplified Binomial Prefix

## Abstract

Floor comparison and exponential separation for a prefix with the simplified exponential denominator.

**Definition 1.1 (Prefix with denominator (1+a)^(rl)).**

Lean statement: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.prefixValue`

*Formalization.* `D5/S3/AnalyticClosure/BinomialMaximumLocalization.prefixValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

prefixValue(a,l,m,r) is the sum of (choose(m,i) a^i)^l over 0<=i<=r, divided by (1+a)^(rl). For l>1 this denominator is not the sum of the powered row-r terms in the published ratio.

**Theorem 1.2 (Floor comparison with a positive limiting constant).**

Lean statement: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.floor_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialMaximumLocalization.floor_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

For fixed a>0 and positive natural l, put q=a/(1+2a) and B=(1+2a)/(1+a). Then prefixValue(a,l,m,floor(mq)) B^(-ml) sqrt(2 pi m q(1-q))^l tends to 1/(1-(1+a)^(-l)). The floor is the natural floor.

**Theorem 1.3 (Uniform separation away from the limiting slope).**

Lean statement: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.separated_prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialMaximumLocalization.separated_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

For a>0, every natural l (including zero), epsilon>0, m>0 and 0<=r<=m with |r/m-a/(1+2a)|>=epsilon, prefixValue(a,l,m,r)/B^(ml) is at most (m+1) exp(-l m min(epsilon^2/2, epsilon log(1+a)/2)), where B=(1+2a)/(1+a). Both boundary indices are covered.

**Theorem 1.4 (Slope and endpoint factor for every maximizing choice).**

Lean statement: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.maximizer_slope_and_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialMaximumLocalization.maximizer_slope_and_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

For fixed a>0 and positive natural l, any r(m)<=m maximizing prefixValue over every 0<=j<=m satisfies r(m)/m -> a/(1+2a). Along that same sequence, the truncated numerator divided by its powered endpoint term tends to 1/(1-(1+a)^(-l)). Ties are allowed. This concerns the simplified prefix only and supplies neither an exact maximizing index nor the Gaussian prefactor for the actual powered-ratio maximum.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.floor_comparison`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.maximizer_slope_and_endpoint`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.prefixValue`
- Truth anchor: `D5/S3/AnalyticClosure/BinomialMaximumLocalization.separated_prefix_bound`
- Dependency: [D5/S3/AnalyticClosure/BinomialLocalGaussian](BinomialLocalGaussian.md)
- Dependency: [D5/S3/AnalyticClosure/BinomialMovingEndpoint](BinomialMovingEndpoint.md)
