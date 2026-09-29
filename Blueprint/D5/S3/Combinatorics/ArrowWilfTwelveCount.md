# Decorated Objects for the First Pattern

## Abstract

Decorated data insert decreasing lower entries around an upper permutation skeleton, giving avoiders with a prescribed largest fixed point.

**Definition 1.1 (The standard support).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.fullSupport`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.fullSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The support consists of the natural numbers from one through n.

**Definition 1.2 (Entries below m).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerSupport`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The lower support consists of the natural numbers from one through m minus one.

**Definition 1.3 (Entries above m).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.upperSupport`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.upperSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The upper support consists of the natural numbers from m plus one through n.

**Definition 1.4 (Gaps forced positive).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.fixedGapLabels`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.fixedGapLabels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The labels are precisely upper-skeleton values outside K whose hat cycle is a singleton; their following gaps must be positive.

**Definition 1.5 (Decorated data for a largest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.TwelveData`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.TwelveData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The data choose k upper values K, a word on the full upper support whose exact fixed-point set is the complement of K, a bound requiring that complement to have at most m minus one values, and a gap vector of total m minus one that is positive at those fixed-point labels.

**Definition 1.6 (The decreasing lower word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerDescending`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerDescending` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The list contains m minus one down through one, in decreasing order.

**Definition 1.7 (The decorated output word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Interleave successive blocks of the decreasing lower word after the chosen upper skeleton, with an initial block before m and m immediately before the first upper entry.

**Theorem 1.8 (The output uses each value once).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For one at most m at most n, the decorated output permutes the standard support from one through n.

**Theorem 1.9 (The distinguished value is fixed).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_fixed_m`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_fixed_m` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Under the support bounds, hat fixes m in the decorated output.

**Theorem 1.10 (No upper value remains fixed).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_no_upper_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_no_upper_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Each upper singleton block receives a lower entry after it, while non-singleton blocks remain non-singleton; hence no value greater than m is hat-fixed.

**Theorem 1.11 (The decorated output avoids the first pattern).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The output avoids (12; 3 to 3): all lower entries are decreasing and there is no fixed point above m.

**Definition 1.12 (An avoiding word with largest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveWord`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The decorated list is packaged as a word on the full support that avoids the first pattern and has largest hat-fixed value m.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.TwelveData`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.fixedGapLabels`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.fullSupport`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerDescending`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.lowerSupport`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_avoids`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_fixed_m`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_no_upper_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveList_perm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.twelveWord`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCount.upperSupport`
- Dependency: [D5/S3/Combinatorics/ArrowWilfGapData](ArrowWilfGapData.md)
