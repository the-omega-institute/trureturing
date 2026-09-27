# The Arrow-Wilf Equivalence

## Abstract

The avoidance classes of the two three-letter arrow patterns have equal cardinality in every positive degree.

**Theorem 1.1 (The two patterns are equinumerous).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfEquivalence.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-yu-arrow-wilf-equivalence` (proved) by `D5/S3/Combinatorics/ArrowWilfEquivalence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-yu-arrow-wilf-equivalence","declaration_gid":"D5/S3/Combinatorics/ArrowWilfEquivalence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For each positive n, the two avoidance counts equal the respective finite formulas F1(n) and F2(n). Their correction terms both equal the same finite signed sum E(n), so the cardinalities agree.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfEquivalence.result`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveFormula](ArrowWilfTwelveFormula.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula](ArrowWilfTwentyThreeFormula.md)
