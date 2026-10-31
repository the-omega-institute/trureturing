---
bibkey: braams2026barnesmittagport
authors: Bastiaan J Braams; The Tau Ceti contributors
year: 2026
title: Gamma vertical bounds and Barnes-kernel sine estimates
doi: null
url: https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f
claim: "Gamma product estimates and sine lower bounds give integrable exterior Barnes kernels."
strata_touched:
  - D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds
  - D5/S3/Analytic/Asymptotics/BarnesSineBounds
  - D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability
  - D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
license: Apache-2.0
triage: anchor
---

## Verified locator

Source: https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f

The immutable source files are `DLMF/Gamma/Products.lean`,
`DLMF/Gamma/SpecialValues.lean`, `DLMF/Gamma/VerticalBounds.lean`, and
`DLMFMathlib/Analysis/Complex/BarnesResidue.lean`. The exact declarations and
consumers below identify the selected proof slice; no DLMF package import is used.
The product and half-line formulas correspond to DLMF 5.8.3 and 5.4.4.

## License and source identity

Each selected DLMF file carries “Copyright (c) 2026 Bastiaan J Braams. All rights
reserved”, “Authors: Bastiaan J Braams” and an explicit Apache 2.0 release grant.
The complete Apache License 2.0 terms are distributed in the repository root
`LICENSE`. The adapted files retain the notices and prominently identify the
changed namespace, imports and shared exponential-integrability owner. No NOTICE
file occurs in the complete source tree at the cited revision.

The exponential-integrability proof is extracted from the existing
`PairwisePoissonHolonomyEnergy` owner, rather than copied as a second proof.
Its exact supplier is TauCetiProject/TauCeti at
`bbd2f34ff81c827b099c0c58d05372c6091ac050`,
`TauCeti/MeasureTheory/Integral/ExpDecay.lean`, with copyright 2026 The Tau Ceti
contributors and an explicit Apache 2.0 grant. Its former owner retains the
complete license and its Fourier-transform proof. Both consumers call the same
extracted declaration directly.

The Barnes primitive from TauCeti's Perron development is not part of this sine
slice. No Perron, digamma, Gauss-digamma, rational-special-value or balanced-product
proof is imported or copied.

## Signature comparison and consumers

The local Gamma declarations are under
`D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds`; the corresponding
supplier names are under `DLMF.Gamma`. Every listed mathematical telescope and
conclusion is unchanged. Namespace, imports and visibility change; only the two
externally used Gamma estimates are public. Products and special values use
Mathlib's existing Gamma APIs. The exponential-majorant proof calls the shared
D5 integrability owner instead of `TauCeti.integrable_exp_neg_mul_abs`.

| Supplier file and declaration | Immediate mathematical consumer |
| --- | --- |
| Products: `summable_sq_div_add_sq (x y : Real)` | `multipliable_one_add_sq_div_add_sq` |
| Products: `multipliable_one_add_sq_div_add_sq (x y : Real)` | `Gamma_div_Gamma_add_mul_I_sq`, `tendsto_prod_gammaVertProd` |
| Products: `Gamma_div_Gamma_add_mul_I_sq {x y} (hx : forall k, (x : Complex) != -k)` | `norm_Gamma_sq_eq` |
| SpecialValues: `Gamma_mul_Gamma_conj (z : Complex)` | `Gamma_half_add_mul_I` |
| SpecialValues: `Gamma_half_add_mul_I (y : Real)` | `gammaVertProd_half` |
| VerticalBounds: `gammaVertProd (x y : Real) : Real` | product convergence and `norm_Gamma_sq_eq` |
| VerticalBounds: `tendsto_prod_gammaVertProd (x y : Real)` | `one_le_gammaVertProd`, `gammaVertProd_anti` |
| VerticalBounds: `one_le_gammaVertProd (x y : Real)` | `gammaVertProd_half`, `norm_recip_Gamma_sq_le` |
| VerticalBounds: `gammaVertProd_anti {x x'} (hx : 0 < x) (hxx : x <= x') (y : Real)` | `norm_recip_Gamma_sq_le` |
| VerticalBounds: `norm_Gamma_sq_eq {x} (hx : 0 < x) (y : Real)` | `gammaVertProd_half`, `norm_recip_Gamma_sq_le` |
| VerticalBounds: `gammaVertProd_half (y : Real)` | `norm_recip_Gamma_sq_le` |
| VerticalBounds: `cosh_le_exp_abs (t : Real)` | `norm_recip_Gamma_sq_le` |
| VerticalBounds: `norm_recip_Gamma_sq_le {x} (hx : 1/2 <= x) (y : Real)` | `exists_norm_recip_Gamma_le` |
| VerticalBounds: `exists_norm_recip_Gamma_le (X : Real)` | Barnes kernel `exists_line_majorant` |
| VerticalBounds: `integrable_one_add_abs_pow_mul_exp_neg {c} (hc : 0 < c) (K : Nat)` | Barnes kernel `integrable_line` |

The sine slice uses the same mathematical signatures and conclusions as the
supplier's `Complex` namespace. Only `barnesRes_sin_lower_line` is public.

| BarnesResidue declaration | Immediate mathematical consumer |
| --- | --- |
| `barnesRes_sq_norm_sin (x y : Real)` | `barnesRes_abs_sin_mul_cosh_le_norm_sin` |
| `barnesRes_abs_sin_mul_cosh_le_norm_sin (x y : Real)` | `barnesRes_sin_lower_line` |
| `barnesRes_sin_lower_line (x y : Real)` | Barnes kernel `sine_pos`, `exists_line_majorant` |

The extracted `integrable_exp_neg_mul_abs {a : Real} (ha : 0 < a)` retains the
exact original proof body and signature, apart from removing `private`. Its
consumers are the Gamma polynomial-exponential integrability theorem and the
three existing calls in `PairwisePoissonHolonomyEnergy`.

## Mathematical use and boundary

The literal kernel is
`Gamma(s) Gamma(1-s) / Gamma(beta-alpha*s) exp(-s log(-z))`.
Reflection and the reciprocal Gamma strip estimate bound its restriction to
`Re(s)=c` by `C (1+abs(y))^K exp(-delta abs(y))`, where
`delta = pi*(1-alpha/2)-abs(arg(-z))`. When delta is positive and
`sin(pi*c)` is nonzero, this is an integrable majorant. Reciprocal Gamma is
entire, including its zeros; no nonvanishing assumption on its denominator
is imposed. The logarithm is the principal complex logarithm throughout.

The independent beta-continuity argument uses the original literal series and
its existing norm summability. Eventual monotonicity of real Gamma on
`[2,infinity)` gives a fixed summable majorant on each positive compact beta
interval. It requires neither a Barnes identity nor a sector asymptotic.

These ingredients do not identify the Barnes integral with the literal series.
That identity additionally requires the holomorphic residue numerators,
horizontal contour decay and a vanishing moving-left contour. The endpoint
ray limit, its sign, and the all-alpha same-z closed-beta family also require
those analytic bridges. No representation or asymptotic is supplied as a new
hypothesis or axiom.

## Retirement at the repository pin

The consumer pins remain Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The DLMF source uses Lean
4.36.0-rc1 and Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca`;
this is a source port, not a dependency upgrade. Remove each port and use direct
imports when this repository's own pinned Mathlib supplies an equivalent
statement. No upstream acceptance event is a retirement condition.
