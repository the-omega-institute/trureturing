# Acyclic Tests

## Abstract

Acyclic Tests

Relatively representable (affine) maps of functors on rings: pullbacks, closed and open loci. Tests are acyclic; tests and locally constant functions commute with filtered colimits.

**Theorem 1.1 (continuousUpTo_locConstCoeff).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests.continuousUpTo_locConstCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests.continuousUpTo_locConstCoeff` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

If a test ring A is the filtered colimit, as a ring, of test rings A_j, then the Λ-cohomology H^n(h_A) on test rings is the colimit of the H^n(h_{A_j}), for every n.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests.continuousUpTo_locConstCoeff`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/BijectiveComparisons](BijectiveComparisons.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/FilteredColimits](FilteredColimits.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestEnvelope](TestEnvelope.md)
