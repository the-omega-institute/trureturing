# Assumption Registry

| assumption | status | statement_gid | approved_by | approved_at |
|---|---|---|---|---|
| Assumptions.ThreeGap | proven | D5/S1/Phase/ThreeDistance.three_gap | user-sshx-D5-T0019 | 2026-08-13 |
| Assumptions.FourierLaplaceEntire | proven | D5/S3/Fourier/PaleyWiener.fourier_laplace_entire_classic | user-sshx-D5-T0018 | 2026-07-12 |
| Assumptions.WeilExplicitFormula | proven | D5/S3/Weil/ZetaBridge/ClassicExplicitFormula.weil_explicit_formula | user-sshx-D5-T0018 | 2026-07-14 |

`D5-T0019` is discharged by the MIT-licensed upstream formalization ported in
`D5/S1/Phase/ThreeGap` (Copyright (c) 2026 Dirk Kunert,
https://github.com/dkunert/three-gap-theorem-lean); `D5/S1/Phase/ThreeDistance.three_gap`
is the direct application and carries no assumption. Mathematical source: the
Steinhaus three-gap conjecture, proved by V. T. Sos, *Acta Math. Acad. Sci.
Hungar.* 8 (1957), 461-472.

Adoption form and retirement condition, per spec A17.2. The proof is vendored
rather than taken as a Lake dependency because the upstream pins
`leanprover/lean4:v4.29.1` while this repository pins `v4.31.0`, and Lake
resolves one revision per package name under a global toolchain, so the machine
comparison rejects the dependency form outright. Retirement condition, stated
against this repository's own pin so that it can actually fire: delete
`D5/S1/Phase/ThreeGap` and apply the library declaration directly once a mathlib
revision this repository has upgraded to contains an equivalent statement. It is
deliberately not phrased as "delete when upstream accepts it", which A17.2
forbids: mathlib PR #40037 (`feat(NumberTheory): the three-gap (Steinhaus)
theorem`, +625 lines) was closed unmerged on 2026-06-09 under the mathlib
AI-contribution standards, so upstream inclusion carries no determinate date.

`D5-T0018-C` recorded the pinned-mathlib bridge from smooth compact support to
an entire complex Fourier-Laplace transform, and is now `proven`: the bridge is
established natively in `D5/S3/Fourier/PaleyWiener` (parametric-integral
differentiation over pinned mathlib, no axiom). Source: R. E. A. C. Paley and
N. Wiener, *Fourier Transforms in the Complex Domain*, American Mathematical
Society Colloquium Publications 19 (1934). The statement fixes the
angular-frequency kernel `exp(-i*z*x)` and carries only that classical input;
it does not assume a Weil identity or RH.

`D5-T0018-F` is discharged by the hypothesis-free theorem
`Zeta23.WeilEF.EF_lit_zetaZeroConfig` ported from
`anthropics/zeta-23-lean` at immutable commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. The routed bridge
`D5/S3/Weil/ZetaBridge/ClassicExplicitFormula.weil_explicit_formula` translates
the upstream zero subtype, analytic multiplicity, Fourier convention, and
unconditional `tsum` into this repository's frozen `ZeroData`, symmetric
cutoff, and pole/prime/archimedean terms. `D5/S3/Weil/WeilIdentity` applies that
bridge directly and carries no assumption. Source: A. Weil, "Sur les 'formules
explicites' de la theorie des nombres premiers", *Comm. Sem. Math. Univ. Lund*
(M. Riesz volume, 1952), 252-265. Neither theorem asserts positivity, RH, or an
O-6 conclusion.

Adoption form and retirement condition, per spec A17.2. The proof is vendored
rather than taken as a Lake dependency because the upstream pins
`leanprover/lean4:v4.33.0-rc2` and mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`, while this repository pins
`v4.31.0` and mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the
machine comparison therefore rejects the dependency form. The port is
Apache-2.0, Copyright 2026 Anthropic, PBC; the retained license and NOTICE are
`D5/S3/Weil/ZetaCore/LICENSE` and `D5/S3/Weil/ZetaCore/NOTICE`. The NOTICE keeps
the complete derivation chain Zeta23 <- PrimeNumberTheoremAnd <- mathlib, and
ported files retain their source and modification notices. The port obeys the
ordinary GID routing, six-line header, import-order, and capacity rules, and
the bridge theorem's axiom closure contains only `propext`, `Classical.choice`,
and `Quot.sound`. Retirement condition, stated against this repository's own
pin so that it can actually fire: delete the vendored Zeta23 modules and bridge,
then cite the library declaration directly once a mathlib revision this
repository has upgraded to contains an equivalent hypothesis-free explicit
formula. It is deliberately not conditioned on upstream acceptance by mathlib.
