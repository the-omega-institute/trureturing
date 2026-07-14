# Assumption Registry

| assumption | status | statement_gid | approved_by | approved_at |
|---|---|---|---|---|
| Assumptions.ThreeGap | active | D5/X_Assumptions/AxiomDebt.three_gap_classic | user-PR-PD | 2026-07-12 |
| Assumptions.FourierLaplaceEntire | active | D5/X_Assumptions/AxiomDebt.fourier_laplace_entire_classic | user-sshx-D5-T0018 | 2026-07-12 |
| Assumptions.WeilExplicitFormula | active | D5/X_Assumptions/AxiomDebt.weil_explicit_formula_classic | user-sshx-D5-T0018 | 2026-07-14 |

`D5-T0019` records the librarian upstream-formalization issue. Source: the
Steinhaus three-gap conjecture, proved by V. T. Sós, *Acta Math. Acad. Sci.
Hungar.* 8 (1957), 461-472. The pinned mathlib v4.31.0 tree has no three-gap or
three-distance theorem; this row carries that classical result as AxiomDebt.

`D5-T0018-C` records the missing pinned-mathlib bridge from smooth compact
support to an entire complex Fourier-Laplace transform. Source: R. E. A. C.
Paley and N. Wiener, *Fourier Transforms in the Complex Domain*, American
Mathematical Society Colloquium Publications 19 (1934). The registered
statement fixes the angular-frequency kernel `exp(-i*z*x)` and carries only
that classical input; it does not assume a Weil identity or RH.

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
