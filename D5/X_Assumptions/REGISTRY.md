# Assumption Registry

| assumption | status | statement_gid | approved_by | approved_at |
|---|---|---|---|---|
| Assumptions.ThreeGap | proven | D5/S1/Phase/ThreeDistance.three_gap | user-sshx-D5-T0019 | 2026-08-13 |
| Assumptions.FourierLaplaceEntire | proven | D5/S3/Fourier/PaleyWiener.fourier_laplace_entire_classic | user-sshx-D5-T0018 | 2026-07-12 |
| Assumptions.WeilExplicitFormula | active | D5/X_Assumptions/AxiomDebt.weil_explicit_formula_classic | user-sshx-D5-T0018 | 2026-07-14 |

`D5-T0019` is discharged by the MIT-licensed upstream formalization ported in
`D5/S1/Phase/ThreeGap` (Copyright (c) 2026 Dirk Kunert,
https://github.com/dkunert/three-gap-theorem-lean); `D5/S1/Phase/ThreeDistance.three_gap`
is the direct application and carries no assumption.

`D5-T0018-C` recorded the pinned-mathlib bridge from smooth compact support to
an entire complex Fourier-Laplace transform, and is now `proven`: the bridge is
established natively in `D5/S3/Fourier/PaleyWiener` (parametric-integral
differentiation over pinned mathlib, no axiom). Source: R. E. A. C. Paley and
N. Wiener, *Fourier Transforms in the Complex Domain*, American Mathematical
Society Colloquium Publications 19 (1934). The statement fixes the
angular-frequency kernel `exp(-i*z*x)` and carries only that classical input;
it does not assume a Weil identity or RH.

`D5-T0018-F` records the classical Weil explicit formula absent from pinned
mathlib v4.31.0. Source: A. Weil, "Sur les 'formules explicites' de la theorie
des nombres premiers", *Comm. Sem. Math. Univ. Lund* (M. Riesz volume, 1952),
252-265. The G-level foundation signature expands every field of the concrete
`ZeroData`, the smooth/even/compact test conditions, the symmetric cutoff
convergence, the archimedean integrability condition, and the exact formulas
for `zeroSum`, `poleTerm`, `primeTerm`, and `archimedeanTerm`. The I-level
`D5/S3/Weil/WeilIdentity` theorem proves the named specialization in the frozen
angular-frequency convention. Neither statement asserts positivity, RH, or an
O-6 conclusion.
