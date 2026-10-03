# Cigler's Narayana Strip Product Formula

## Abstract

The product of two signed Narayana strip series is the Narayana strip series with squared parameters at heights 4m and 4m + 1.

**Theorem 1.1 (The product formula at both strip heights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-narayana-strip-product` (proved) by `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-narayana-strip-product","declaration_gid":"D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer m and each height h equal to 4m or 4m + 1, C^{(h)}(t^2, z^2) = c^{(h)}(t, z)c^{(h)}(-t, -z) as formal power series in z with coefficients in the integer polynomial ring in t. Here C^{(h)} and c^{(h)} sum Dyck paths confined to heights zero through h, with z marking semilength, every up-step weighted one, and down-step arrival weights repeating 1, t for C^{(h)} and 1, t, -1, -t for c^{(h)}. The equality holds for every coefficient of z and proves Conjecture 2, equation (79), of Cigler's paper. First-return decomposition gives the continuant representation of each bounded series. The numerator and denominator factorizations at indices h + 1, together with invertibility of the denominators, give the product identity.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.result`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries](CiglerStripProductSeries.md)
