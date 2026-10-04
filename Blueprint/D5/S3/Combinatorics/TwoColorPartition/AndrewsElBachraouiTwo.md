# Andrews and El Bachraoui Conjecture Two

## Abstract

The two-color partition series C-prime at parameters 2 and 4 has nonnegative coefficients.

**Theorem 1.1 (Positivity of C-prime).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/andrews-el-bachraoui-c24-positivity` (proved) by `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andrews-el-bachraoui-c24-positivity","declaration_gid":"D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, the coefficient cCoeff 2 4 n is nonnegative. Thus the two-color partition series C-prime with parameters 2 and 4 has no negative coefficient. A finite Heine transformation and partial fractions express the coefficients in terms of divisor counts, a periodic term and weighted alternating sums. Character bounds give nonnegativity for large degrees, and exact evaluation treats the remaining degrees.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine](AndrewsElBachraouiHeine.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted](AndrewsElBachraouiWeighted.md)
