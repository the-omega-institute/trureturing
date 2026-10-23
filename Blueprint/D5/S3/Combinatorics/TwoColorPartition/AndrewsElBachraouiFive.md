# Andrews and El Bachraoui Conjecture Five

## Abstract

Andrews and El Bachraoui Conjecture Five.

**Theorem 1.1 (Complete eventual D-prime coefficient positivity).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result` (`✓ std3`). ∎

*Resolves.* `Problems/andrews-el-bachraoui-dprime-eventual-positivity` (proved) by `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andrews-el-bachraoui-dprime-eventual-positivity","declaration_gid":"D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For all natural k and m, if one is at most m and m is less than k, there exists a natural threshold N such that for every natural n at least N, the original dCoeff k m n is nonnegative. The threshold may depend on k and m. Both parities and both endpoint families are included. The exact source transformation supplies a fixed rational series minus a Gauss convolution series. Arithmetic-progression summation proves the rational coefficient limit on every n and propagates a sharp upper sequence for the product coefficients. Finite subset integration computes the rational leading constant, and the strict Wallis gap makes the difference eventually positive. No radial-to-coefficient inference or unproved analytic premise is used.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFive.result`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants](AndrewsElBachraouiFiveConstants.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveGauss](AndrewsElBachraouiFiveGauss.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveReduction](AndrewsElBachraouiFiveReduction.md)
