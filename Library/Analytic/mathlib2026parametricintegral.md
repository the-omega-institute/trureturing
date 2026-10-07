---
bibkey: mathlib2026parametricintegral
authors: The mathlib contributors
year: 2026
title: "Mathlib parametric integral differentiation"
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ParametricIntegral.lean
claim: "The pinned dominated local derivative theorem differentiates an integral under a common measurable, integrable local envelope; it does not prove the actual FIB kernel hypotheses or its signed arithmetic budget."
strata_touched: []
license: citation-only
triage: anchor
---

# The existing parameter derivative theorem

The source is pinned Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, input tag `v4.33.0`.
The exact source path is
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`.

The existing declaration
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` assumes a neighborhood
of the parameter, almost-everywhere strong measurability, integrability
at the reference parameter, measurable derivative, pointwise derivatives
throughout that neighborhood and a uniform integrable derivative bound.
The stronger wording is essential: parameterwise differentiability alone
does not supply the interchange. The file also contains the corresponding
local Lipschitz and Fréchet derivative variants.

FIB §398 keeps $y\ge1$ fixed and differentiates the high-quotient term

$$
\frac{R(y)}{s y^2}
\left[\frac1{\log s+\log y}
+\frac1{(\log s+\log y)^2}\right].
$$

For a common positive neighborhood of $s>x>1$, both this integrand and
its parameter derivative have a constant multiple of $|R(y)|/y^2$
as envelope. The established actual residual estimate makes that
envelope integrable. This is the manuscript's proposed application of
the classical theorem; no complete Lean application to the actual
FIB definitions has been compiled here. The low-quotient integral,
actual high moment and final $H_m$-weighted sign remain separate
obligations. The source theorem is reused rather than renamed or
delivered as a new wrapper.
