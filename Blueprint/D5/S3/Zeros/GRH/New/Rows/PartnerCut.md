# Partner Cut

## Abstract

Partner Cut

Stabiliser subgroup, data on columns; on that subgroup the datum is a product.

**Theorem 1.1 (columnDatum_mul_ite_eq).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/PartnerCut.columnDatum_mul_ite_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/PartnerCut.columnDatum_mul_ite_eq` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let F be invariant under left multiplication by H = rowStabilizer, z square. Then columnDatum at the columns e of z, times F(y) if FixesColsOff e z and 0 if not, equals χ(det z)F(z⁻¹y) for z ∈ H and 0 otherwise.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/PartnerCut.columnDatum_mul_ite_eq`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/BlockMatrices](../../Lib/General/LinearAlgebra/BlockMatrices.md)
