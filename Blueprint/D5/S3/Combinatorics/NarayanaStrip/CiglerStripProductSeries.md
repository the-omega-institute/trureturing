# Separate Numerator and Denominator Factorizations

## Abstract

At both endpoint indices corresponding to heights 4m and 4m + 1, the Narayana numerator and denominator factor into signed continuants.

**Theorem 1.1 (The four continuant products).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries.product_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries.product_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For t and z in any commutative ring, let P^+(t, z) and Q^+(t, z) be the continuants with coefficients alternating z and tz, and let P^-(t, z) and Q^-(t, z) be the continuants with coefficients repeating z, tz, -z, -tz. Each numerator P has initial values (0, 1), and each denominator Q has initial values (1, 1). For every nonnegative integer m and each index j equal to 4m + 1 or 4m + 2, P^+_j(t^2, z^2) = P^-_j(t, z)P^-_j(-t, -z) and Q^+_j(t^2, z^2) = Q^-_j(t, z)Q^-_j(-t, -z). The endpoint formulas and addition and doubling identities for the second-order recurrence give the two numerator products and the two denominator products.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries.product_factorization`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra](CiglerStripProductAlgebra.md)
