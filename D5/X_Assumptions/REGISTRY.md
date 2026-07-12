# Assumption Registry

| assumption | status | statement_gid | approved_by | approved_at |
|---|---|---|---|---|
| Assumptions.ThreeGap | active | D5/X_Assumptions/AxiomDebt.three_gap_classic | user-PR-PD | 2026-07-12 |
| Assumptions.FourierLaplaceEntire | active | D5/X_Assumptions/AxiomDebt.fourier_laplace_entire_classic | user-sshx-D5-T0018 | 2026-07-12 |

`D5-T0019` records the librarian upstream-formalization issue. Source: the
Steinhaus three-gap conjecture, proved by V. T. Sós, *Acta Math. Acad. Sci.
Hungar.* 8 (1957), 461-472. The pinned mathlib v4.31.0 tree has no three-gap or
three-distance theorem; this row carries that classical result as AxiomDebt.

`D5-T0018-C` records the missing pinned-mathlib bridge from smooth compact
support to an entire complex Fourier-Laplace transform. The registered
statement fixes the angular-frequency kernel `exp(-i*z*x)` and carries only
that classical Paley-Wiener input; it does not assume a Weil identity or RH.
