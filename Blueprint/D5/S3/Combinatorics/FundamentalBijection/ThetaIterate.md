# Enumeration of Iterated 132-Avoiders

## Abstract

Avoidance of 132 through successive iterates has a cubic quasipolynomial count followed by linear and constant counts.

**Theorem 1.1 (The counts through every iteration depth).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result` (`✓ std3`). ∎

*Resolves.* `Problems/archer-laudone-theta-iterate-132` (proved) by `D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-laudone-theta-iterate-132","declaration_gid":"D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Let t(n,k) count the permutations of size n whose iterates from zero through k under the fundamental bijection all avoid 132. For n at least two, t(n,2) is m cubed + 3m squared + 2m - 1 when n = 3m, m cubed + 4m squared + 4m when n = 3m + 1, and m cubed + 5m squared + 7m + 2 when n = 3m + 2. For n at least three, t(n,3) = 3n - 4, t(n,4) = 2n - 1, t(n,5) = n + 2, and t(n,k) = 5 for every k at least six.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDecomposition](ThetaIterateDecomposition.md)
