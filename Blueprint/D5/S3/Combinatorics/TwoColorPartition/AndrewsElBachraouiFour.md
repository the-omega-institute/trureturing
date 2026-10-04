# Andrews and El Bachraoui Conjecture Four

## Abstract

The two-color partition series D-prime at parameters 2 and 3 has negative coefficients exactly at degrees 10 and 22.

**Theorem 1.1 (The two negative coefficients of D-prime).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/andrews-el-bachraoui-d23-sign-pattern` (proved) by `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andrews-el-bachraoui-d23-sign-pattern","declaration_gid":"D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, the coefficient dCoeff 2 3 n is negative if and only if n is 10 or 22. Thus the two-color partition series D-prime with parameters 2 and 3 has precisely these two negative coefficients. A finite Heine transformation reduces the coefficients to triangular-pair counts and alternating odd divisor sums; their bounds give nonnegativity for large degrees, and exact evaluation treats the remaining degrees.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter](AndrewsElBachraouiCharacter.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine](AndrewsElBachraouiHeine.md)
