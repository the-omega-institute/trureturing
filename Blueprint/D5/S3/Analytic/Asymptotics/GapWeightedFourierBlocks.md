# Fourier recovery on long mesh blocks

## Abstract

Long late mesh blocks recover Fourier coefficients uniformly.

**Definition 1.1 (Gap-weighted block average).**

Lean statement: `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.blockAverage`

*Formalization.* `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.blockAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real mesh y, complex samples f and natural indices a and b, sum (y(k+1)−y(k))f(k) over a≤k<b and divide by y(b)−y(a). The quotient is zero when the span is zero.

**Theorem 1.2 (Uniform recovery at a chosen frequency).**

Lean statement: `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.eventually_blockAverage_modulated_series`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.eventually_blockAverage_modulated_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let y be a strictly increasing real mesh with gaps tending to zero. Let c(i) be absolutely summable complex coefficients on an arbitrary index type with real frequencies f(i). Suppose the samples s(k) differ from the sum of c(i) exp(i f(i)y(k)) by an error tending to zero. For each real ν and each ε>0 there exist an index A and a span H>0. For every A≤a<b with y(b)−y(a)≥H, the gap-weighted block average of s(k) exp(−iνy(k)) differs from the sum of c(i) over f(i)=ν by at most ε.

At a nonzero shifted frequency μ, comparison with the phase primitive bounds the normalized contribution by 2/(|μ|(y(b)−y(a))) plus |μ| times the largest gap in the block. The boundary term comes from telescoping the primitive. Use this estimate for a finite set of frequencies and bound the rest by their absolute coefficient mass. The total gap weight is the block span, so a uniform bound on the late sample errors also bounds their normalized contribution.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.blockAverage`
- Truth anchor: `D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks.eventually_blockAverage_modulated_series`
- Dependency: [D5/S3/Analytic/Asymptotics/GapWeightedFourier](GapWeightedFourier.md)
