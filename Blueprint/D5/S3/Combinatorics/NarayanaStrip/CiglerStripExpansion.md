# Cigler's Even-Strip Expansions

## Abstract

Cigler's two expansions express the Narayana-weighted Dyck path sums in an even strip through bounded Dyck skeletons and binomial coefficients.

**Theorem 1.1 (The Narayana and signed expansions).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-narayana-strip-expansion` (proved) by `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-narayana-strip-expansion","declaration_gid":"D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer m and nonnegative integer n, let A_j count Dyck paths of semilength j in the strip of height m minus one. Give each up-step weight one and each down-step arriving at height k the Narayana weight one for even k and t for odd k. The weighted sum for paths of semilength n plus one in the strip of height 2m equals the sum, over j from zero through floor(n/2), of A_j times binom(n, 2j) times t^j times (1 + t)^(n - 2j). With the arrival weights instead repeating 1, t, minus one and minus t, the sum equals the sum over the same range of (-1)^j times A_j times binom(floor(n/2), j) times t^j times (1 + t)^(n - 2j). These polynomial identities are Conjecture 3 of Cigler's paper. Pairing the interior steps gives a Motzkin path in the strip of height m minus one. Removing horizontal steps gives a Dyck skeleton and colored gaps; counting all gap fillings yields the first expansion, while sign-reversing cancellation and counting the fixed gaps yield the second.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting](CiglerStripExpansionCounting.md)
