# Split Prime Reciprocity

## Abstract

Split Prime Reciprocity

Power residue symbols of S-units give exactly the relations on tame ramification of cocycles.

**Theorem 1.1 (power_residue_reciprocity).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.power_residue_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.power_residue_reciprocity` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let U fix V, mV = 0, γ_i satisfy IsTameGeneratorFor, and ζ^(b(y)_i) = φ_i r/r for N-units y = r^m. Trivialised cocycles z obey ∑ b(gy)_i g⁻¹z(γ_i) = 0 and vanish on U if all z(γ_i) = 0. For totally complex fixed field, ∑ b(gy)_i f(i,g) = 0 for all y makes (∑_g f(i,g) ga)_i some (z(γ_i))_i.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.power_residue_reciprocity`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/EquivariantUnits](EquivariantUnits.md)
