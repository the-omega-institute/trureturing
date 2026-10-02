# Fixed Avoiders of the Third Iterate

## Abstract

The generating functions for 231- and 312-avoiders fixed by the third iterate of the fundamental bijection are rational.

**Theorem 1.1 (The third-iterate generating function).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result` (`✓ std3`). ∎

*Resolves.* `Problems/archer-laudone-theta-cube-231-312` (proved) by `D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-laudone-theta-cube-231-312","declaration_gid":"D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For each pattern sigma equal to 231 or 312, the ordinary generating function for sigma-avoiding permutations fixed by the third iterate of the fundamental bijection, multiplied by 1 - x - x squared - 2x cubed, equals one.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors](ThetaBasicSumFactors.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Boundary](ThetaCube231Boundary.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargeFinish](ThetaCube231LargeFinish.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix](ThetaCube231LargePrefix.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Return](ThetaCube231Return.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231SecondReturn](ThetaCube231SecondReturn.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Shape](ThetaCube231Shape.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Classify](ThetaCube312Classify.md)
