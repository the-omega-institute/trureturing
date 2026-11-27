# Fischer Decomposition

## Abstract

Fischer Decomposition

Swap symmetry, vacuum weight, Laplacians and Fischer inner product for Howe's argument.

**Theorem 1.1 (fockLaplacian_eq_zero_of_isKHighest).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/FischerDecomposition.fockLaplacian_eq_zero_of_isKHighest`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/FischerDecomposition.fockLaplacian_eq_zero_of_isKHighest` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let P be K-highest of weight ν for the oscillator action on rows, Q_ab = Σ ∂_{ac}∂_{bc}P over c with σε_aε'_c = +. If no nonzero Q_ab, ε_a ≠ ε_b, is K-highest of weight ν − e_a + e_b, all these Q_ab vanish.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/FischerDecomposition.fockLaplacian_eq_zero_of_isKHighest`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/HighestVectors](../Rigidity/HighestVectors.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/OscillatorDefs](OscillatorDefs.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Nabla](../../GLn/SchurModule/Nabla.md)
