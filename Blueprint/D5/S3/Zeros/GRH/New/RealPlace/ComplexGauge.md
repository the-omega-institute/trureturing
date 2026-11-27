# Complex Gauge

## Abstract

Complex Gauge

Tower measure at C is Haar with constant bound; level and gauge at C.

**Theorem 1.1 (exists_orthonormal_ker_lintegral_le).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/ComplexGauge.exists_orthonormal_ker_lintegral_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/ComplexGauge.exists_orthonormal_ker_lintegral_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let n = ϱ+1, |ι| = s+1+3n ≤ L, L ≥ 4, and rank C ≤ 3n. Some matrix O with orthonormal columns has CO = 0 and, for all j, the integral of (36/|Oᴴu|²)^s over the u in ℂ^ι with all |u_i| ≤ L^j is at most L^{198n(j+1)}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/ComplexGauge.exists_orthonormal_ker_lintegral_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/ComplexFloorMeasure](../../Lib/DiscreteSeries/Bruhat/ComplexFloorMeasure.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/StableCells](../Filling/StableCells.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/LevelGauge](LevelGauge.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/SobolevCell](SobolevCell.md)
