# Counting

## Abstract

Counting

Flag count; amplification bounds dimension of conditioned forms by flags times lattice points. Parahoric index times dim TwistingData.excessCond is at most (1+κ)m^N; size conditions. Forms deep in all frames are rare: their mean depth is small.

**Theorem 1.1 (sum_finrank_deepForms_le).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/Counting.sum_finrank_deepForms_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/Counting.sum_finrank_deepForms_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let K have characteristic p and assume HeckeSizes. Then for every M, ∑_{d<M} dim V_d ≤ (1 + z)·m^N, where V_d = TwistingData.deepForms n r d and m is the number of monomials of degree n in k variables.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/Counting.sum_finrank_deepForms_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars](../../Lib/LocalGL/Green/CuspidalAtScalars.md)
- Dependency: [D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors](FrobeniusFactors.md)
- Dependency: [D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone](InterlacingCone.md)
