# The quadratic character modulo four

## Abstract

Finite character convolution gives a uniform weighted Mangoldt estimate modulo four.

**Theorem 1.1 (Character prefixes).**

Lean statement: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.sum_chi_four_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.sum_chi_four_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the character over the positive integers up to X is the parity of floor((X+1)/2). It therefore belongs to {0,1}. The same prefix identity is used in the two alternating divisor hyperbola estimates.

**Remark 1.2 (The classical bounded character sum).**

Lean statement: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve`

*Formalization.* `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve` (`✓ std3`).

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

Apostol, Introduction to Analytic Number Theory, Chapter 7, Dirichlet's theorem on primes in arithmetic progressions, uses boundedness of the sum chi(n)*Lambda(n)/n for a nonprincipal character in the proof of Theorem 7.3. For chi modulo four this is the classical O(1) statement. The locator for this intermediate step is Chapter 7; no separate lemma number or page is asserted. The explicit constant twelve and the finite-convolution derivation below are repo-derived quantitative details.

**Theorem 1.3 (A bounded signed Mangoldt sum).**

Lean statement: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

The classical Leibniz formula, supplied by Mathlib's Real.tendsto_sum_pi_div_four, gives the natural-order limit pi/4. Alternating partial-sum bounds give the harmonic character tail at y at most 1/y. No unconditional summability of the unpaired harmonic character series is used.

The logarithmic character sum is bounded using the decrease of log(t)/t for t at least three. Finite Dirichlet convolution expresses it as the weighted Mangoldt sum convolved with the harmonic character prefix. The tail estimate and the ordinary Chebyshev upper bound control the convolution error by six. Since pi/4 is at least two thirds, the signed weighted Mangoldt sum has absolute value at most twelve. This explicit bound and finite-convolution presentation are repo-derived; the underlying boundedness statement is classical.

## References

- Truth anchor: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve`
- Truth anchor: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve`
- Truth anchor: `D5/S3/PrimeGaps/ChiFourWeightedMangoldt.sum_chi_four_prefix`
