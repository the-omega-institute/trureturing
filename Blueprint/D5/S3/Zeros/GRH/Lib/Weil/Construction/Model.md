# Model

## Abstract

Model

L¹ (Feichtinger) space of vacuum coefficients, Heisenberg representation, reproducing formula, Schur's lemma.

**Theorem 1.1 (integral_form_eq_mul_modelInner).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Construction/Model.integral_form_eq_mul_modelInner`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Construction/Model.integral_form_eq_mul_modelInner` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Uniqueness of the invariant form: if B_z are bounded sesquilinear forms on the reproducing space, z ↦ B_z(v,w) is integrable and ∫B_z dν is invariant under all ρ(x), then ∫B_z(v,w) dν = (∫B_z(vac,vac) dν)·⟨v,w⟩.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Construction/Model.integral_form_eq_mul_modelInner`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HaarUnique](../../General/LinearAlgebra/HaarUnique.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Construction/SubmoduleNormedSpace](SubmoduleNormedSpace.md)
