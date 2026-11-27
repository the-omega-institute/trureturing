# Unramified Characters

## Abstract

Unramified Characters

Prime induced by a p-adic embedding; extension to the completion and finite adeles. Unique unramified character with given value at Frobenius; uniform local constancy.

**Theorem 1.1 (existsUnique_unramified_char).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters.existsUnique_unramified_char`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters.existsUnique_unramified_char` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let Γ be the absolute Galois group of a local field k and φ an arithmetic Frobenius. For every r in ℚ/ℤ there is exactly one continuous character χ : Γ → ℚ/ℤ that is trivial on inertia and has χ(φ) = r.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters.existsUnique_unramified_char`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalExtension](LocalExtension.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/AdicRingHomExt](../../General/Algebra/AdicRingHomExt.md)
