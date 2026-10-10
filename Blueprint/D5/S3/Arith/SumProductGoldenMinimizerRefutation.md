# O'Bryant's Golden Minimizer Question Is Refuted

## Abstract

A seven-point positive-real set with at most seventeen products can have at most twenty-two sums, while the corresponding golden set has at least twenty-four.

**Definition 1.1 (Golden power set).**

Lean statement: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.goldenSet`

*Formalization.* `D5/S3/Arith/SumProductGoldenMinimizerRefutation.goldenSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, goldenSet n is the image of the integers from one through n under the powers of the real golden ratio.

**Definition 1.2 (Golden minimizer claim).**

Lean statement: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.claim`

*Formalization.* `D5/S3/Arith/SumProductGoldenMinimizerRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n at least three, every positive n-element finite set A whose product set has cardinality at most 3n minus 4 has a sum set at least as large as the sum set of goldenSet n.

**Theorem 1.3 (A plastic-root counterexample).**

Lean statement: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumProductGoldenMinimizerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/obryant-2024-golden-minimizer-refutation` (refuted) by `D5/S3/Arith/SumProductGoldenMinimizerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"obryant-2024-golden-minimizer-refutation","declaration_gid":"D5/S3/Arith/SumProductGoldenMinimizerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The real root r in the interval (1,2) of r cubed minus r minus one equals zero yields A equal to the seven powers with exponents 0, 3, 5, 6, 7, 8 and 9. Products lie in the image of the sixteen-element exponent sumset, so their cardinality is at most seventeen.

The identities obtained from r cubed equal r plus one are encoded by coefficient vectors in the integers cubed. Their pointwise sumset has twenty-two vectors, and evaluation at r covers A+A. The existing geometric seven-term bound gives at least twenty-four sums for the golden set at n equal to seven. These inequalities contradict the claim.

## References

- Truth anchor: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.claim`
- Truth anchor: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.goldenSet`
- Truth anchor: `D5/S3/Arith/SumProductGoldenMinimizerRefutation.result`
- Dependency: [D5/S3/Arith/SumProductSevenPointCell](SumProductSevenPointCell.md)
