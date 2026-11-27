# Local Statement

## Abstract

Local Statement

Scaled Hecke operator passes the chain; divisibility on its image at non-split primes. Explicit bound for all conjugates of the untwisted chain of lifts. Chain of lifts is divisible by predicted p-power on a submodule of small index.

**Theorem 1.1 (exists_indexDvd_Bmu_divisible).**

Lean statement: `D5/S3/Zeros/GRH/New/Columns/LocalStatement.exists_indexDvd_Bmu_divisible`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Columns/LocalStatement.exists_indexDvd_Bmu_divisible` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For an integer β < gain(p) − err(p) + 1 (err = Data.allowedLoss; gain omitted unless p < x₁ is non-split), some O_ι-module S of columns has index (IndexDvd) dividing p^l, l ≤ err(p)·dim, in the ι-integral columns, and v(B_μφ) ≥ β for ramified φ ∈ S, all twists with Q prime to p, all good Ψ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Columns/LocalStatement.exists_indexDvd_Bmu_divisible`
- Dependency: [D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType](MarkedPrimeType.md)
- Dependency: [D5/S3/Zeros/GRH/New/Columns/SizeEstimates](SizeEstimates.md)
