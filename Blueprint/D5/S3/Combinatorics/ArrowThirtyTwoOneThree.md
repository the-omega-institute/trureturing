# Enumeration of (32; 1 to 3) Avoiders

## Abstract

The (32; 1 to 3) avoidance series satisfies a cubic equation and is its distinguished formal branch.

**Theorem 1.1 (The cubic enumeration).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-yu-arrow-32-13-enumeration` (proved) by `D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-yu-arrow-32-13-enumeration","declaration_gid":"D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The generating series F of the (32; 1 to 3) avoidance numbers satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0. It is the unique integer formal power series satisfying this equation with constant coefficient one and coefficient of x equal to one.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra](ArrowThirtyTwoOneThreeAlgebra.md)
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs](ArrowThirtyTwoOneThreeDefs.md)
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined](ArrowThirtyTwoOneThreeRefined.md)
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeSeries](ArrowThirtyTwoOneThreeSeries.md)
