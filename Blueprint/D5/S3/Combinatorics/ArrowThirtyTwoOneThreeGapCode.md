# Encoding the Value Gaps

## Abstract

Selected last-cycle letters divide the complementary prefix into independent value intervals.

**Definition 1.1 (Selected letters and prefix).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.GapData`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.GapData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A gap datum on 1 through n consists of k strictly increasing selected letters and a complementary prefix with closed edges; together the two words permute the entire interval.

**Definition 1.2 (Inserting the first selected letter).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Choose an initial avoiding word of length i and a gap datum on the remaining translated values. Placing the first selected letter after that initial interval gives a gap datum with one more selected letter.

**Theorem 1.3 (Unique first-gap decomposition).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every n and k, this first-gap insertion is bijective: the first selected letter determines the initial interval and the translated remainder uniquely.

**Theorem 1.4 (Counting gap data).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.gapData_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.gapData_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The number of gap data with k selected letters among n plus k values equals the coefficient of x to the n in the (k plus one)st power of the avoidance series.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.GapData`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.gapData_card`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.joinGap_bijective`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps](ArrowThirtyTwoOneThreeBijectionGaps.md)
