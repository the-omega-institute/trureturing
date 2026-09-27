# Full-Type Geometric Saturation

## Abstract

Schroeder's geometric saturation bound for injectively indexed nonzero cofactor types.

**Theorem 1.1 (Each nonzero type has total geometric weight at most one).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes.saturation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes.saturation_bound` (`✓ std3`). ∎

*Citation.* Michael Schroeder (2026). *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. DOI: [10.5281/zenodo.22760638](https://doi.org/10.5281/zenodo.22760638). URL: <https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip>.

*Commentary.*

This is a source transplant of Michael Schroeder's Erdos7.CappedGain.saturation_bound. Its copyright, full MIT license and source correspondence appear in `D5/L/Arith/schroeder2026noncoverage`.

Let A be an arbitrary finite label family, I any finite index type with a distinguished zero, and p a rational number at least one. Assume the pair of index and depth is injective on A, every index is nonzero, and every depth lies between one and an arbitrary finite bound D. The sum of beta(p, depth), where beta(p,e) is (p-1)/p^e, is at most the cardinality of I minus one.

The proof embeds the family into nonzero index-depth pairs and sums the finite geometric series in each index fiber. It imposes no sparsity condition on the index type. For a product of bounded exponent sets, the ordinary Mathlib cardinality theorem supplies the product of the coordinate sizes directly inside an application. No specialized cofactor wrapper is added by this transplant.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes.saturation_bound`
