# An Explicit Lucas Growth Threshold

## Abstract

Odd-index Lucas growth crosses an explicit square-obstruction threshold.

**Theorem 1.1 (Growth beyond the square-obstruction bound).**

Lean statement: `D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r at least 119 and every index n at least 2r+1, the square of the Lucas number L_n exceeds 128 times 6^r plus four. The odd-index subsequence grows by a factor of at least five halves at each step. An exact integer comparison at r=119 then places its square above the stated exponential bound, and Lucas monotonicity extends the result to later indices.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold`
