---
bibkey: braams2026barnesmittagport
authors: Bastiaan J Braams; The Tau Ceti contributors
year: 2026
title: Gamma bounds and Mellin-Barnes contour closure
doi: null
url: https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f
claim: "Gamma estimates, explicit pole numerators and contour closure identify the literal exterior Barnes integral."
strata_touched:
  - D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds
  - D5/S3/Analytic/Asymptotics/BarnesSineBounds
  - D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability
  - D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
  - D5/S3/Analytic/Asymptotics/BarnesResidue
  - D5/S3/Analytic/Asymptotics/MellinBarnesSeries
license: Apache-2.0
triage: anchor
---

## Verified locator

Source: https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f

The immutable source files are `DLMF/Gamma/Products.lean`,
`DLMF/Gamma/SpecialValues.lean`, `DLMF/Gamma/VerticalBounds.lean`, and
`DLMFMathlib/Analysis/Complex/BarnesResidue.lean` and
`DLMFMathlib/Analysis/Complex/MellinBarnesSeries.lean`. The exact declarations and
consumers below identify the selected proof slice; no DLMF package import is used.
The product and half-line formulas correspond to DLMF 5.8.3 and 5.4.4.

## License and source identity

Each selected DLMF file carries “Copyright (c) 2026 Bastiaan J Braams. All rights
reserved”, “Authors: Bastiaan J Braams” and an explicit Apache 2.0 release grant.
The complete source tree at the cited revision has no LICENSE, NOTICE or
COPYING-named file. Each selected file carries the explicit Apache 2.0 grant
quoted above. This repository distributes the complete Apache License 2.0 terms
in its root `LICENSE`. The adapted files retain the notices and prominently
identify the changed namespace, imports and shared exponential-integrability
owner.

The exponential-integrability proof is extracted from the existing
`PairwisePoissonHolonomyEnergy` owner, rather than copied as a second proof.
Its exact supplier is TauCetiProject/TauCeti at
`bbd2f34ff81c827b099c0c58d05372c6091ac050`,
`TauCeti/MeasureTheory/Integral/ExpDecay.lean`, with copyright 2026 The Tau Ceti
contributors and an explicit Apache 2.0 grant. Its former owner retains the
complete license and its Fourier-transform proof. Both consumers call the same
extracted declaration directly.

The reciprocal primitive in the selected Barnes contour proof has the supplier's
TauCeti Perron provenance. The exact TauCeti source is
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Perron/Basic.lean` at
`a049b4264d2cf4dbf4720796f844a3a3764914a5`; its arctangent/logarithm
primitive differs by the Perron-integrand rewrite. The Barnes port retains both
Braams and Tau Ceti copyright notices. The complete TauCeti tree at that
revision has a root Apache LICENSE and no NOTICE or COPYING-named path;
the license is byte-identical to the pinned Mathlib Apache license.
The selected ports distribute the complete terms through this repository's
existing root LICENSE. Digamma, Gauss-digamma, rational-special-value and
balanced-product proofs are outside the selected slice.

## Signature comparison and consumers

The local Gamma declarations are under
`D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds`; the corresponding
supplier names are under `DLMF.Gamma`. Every listed mathematical telescope and
conclusion is unchanged. Namespace, imports and visibility change; only the three
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
| VerticalBounds: `norm_recip_Gamma_sq_le {x} (hx : 1/2 <= x) (y : Real)` | `exists_norm_recip_Gamma_le`, literal kernel `norm_line_le_recip_gamma` |
| VerticalBounds: `exists_norm_recip_Gamma_le (X : Real)` | Barnes kernel `exists_line_majorant` |
| VerticalBounds: `integrable_one_add_abs_pow_mul_exp_neg {c} (hc : 0 < c) (K : Nat)` | Barnes kernel `integrable_line` |

The sine slice uses the same mathematical signatures and conclusions as the
supplier's `Complex` namespace. The two externally consumed sine lower bounds are public.

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
`[2,infinity)` gives a fixed summable majorant on every compact real beta
interval. It requires neither a Barnes identity nor a sector asymptotic.

The literal-kernel source constructs `leftNumerator` from shifted Gamma,
Gamma(1-s), entire reciprocal Gamma, the principal-logarithm exponential and
the finite product over j<n. It is holomorphic on the closed n-th strip;
the kernel equals this numerator divided by s+n away from s=-n. Its value
at -n is exactly z^n/Gamma(alpha*n+beta), also when reciprocal Gamma is zero.

Uniform finite-strip bounds give both horizontal limits. On the moving-left
line at beta=alpha-1 the retained denominator is Gamma(alpha*n+alpha/2-1).
For n=m+1, fixed-beta summability at betaPrime=3*alpha/2-1 forces the actual
line integral to zero. `source_barnes_identity` supplies all fields of
`MBSeriesData` and uses `mbSeries_hasSum` and the original literal `HasSum`
uniqueness. The normalization is one over 2*pi for integration in dy.

These proof texts are uncompiled source. Native elaboration, axiom closure
and admission are unestablished. The rightward-shift, endpoint-limit and
closed-beta family proof texts described below are also uncompiled. No
representation or asymptotic is inserted as a new hypothesis or axiom.


## Contour slice and actual source consumers

The following additional selected statements have the same mathematical
signatures as the immutable supplier. The first five Barnes contour lemmas,
the Gamma finite-product lemmas and intermediate contour-series lemmas are
private. They are retained for the listed actual consumers, without a
standalone helper freeze.

| Supplier declaration | Local owner and immediate source consumer |
| --- | --- |
| BarnesResidue: `barnesRes_hasDerivAt_primitive` | BarnesResidue: `barnesRes_integral_recip` |
| BarnesResidue: `barnesRes_continuous_recip` | BarnesResidue: `barnesRes_integral_recip` |
| BarnesResidue: `barnesRes_integral_recip` | BarnesResidue: `barnesRes_tendsto_integral_recip` |
| BarnesResidue: `barnesRes_tendsto_integral_recip` | BarnesResidue: `barnesRes_vertical_shift` |
| BarnesResidue: `barnesRes_norm_horizontal_recip_le` | BarnesResidue: `barnesRes_vertical_shift` |
| BarnesResidue: `barnesRes_vertical_shift` | MellinBarnesSeries: `mbSeries_step`; actual kernel `integral_right_step` |
| BarnesResidue: `barnesRes_Gamma_add_nat_succ` | MittagLefflerBarnesKernel: `mbSeries_Gamma_mul_eq_div` |
| BarnesResidue: `barnesRes_prod_nat_sub` | MittagLefflerBarnesKernel: `barnesRes_prod_sub_nat` |
| BarnesResidue: `barnesRes_prod_sub_nat` | MittagLefflerBarnesKernel: `mbSeries_Gamma_residue` |
| BarnesResidue: `barnesRes_abs_sinh_le_norm_sin` | BarnesSineBounds: `barnesRes_sin_lower_far` |
| BarnesResidue: `barnesRes_sin_lower_far` | MittagLefflerBarnesKernel: `exists_horizontal_majorant` |
| BarnesResidue: `barnesRes_tendsto_poly_exp` | MittagLefflerBarnesKernel: `horizontal_tendsto_zero` |
| MellinBarnesSeries: `MBSeriesData` | MellinBarnesSeries shift chain; actual construction inside `source_barnes_identity` |
| MellinBarnesSeries: `mbSeries_step` | MellinBarnesSeries: `mbSeries_sub_eq_sum` |
| MellinBarnesSeries: `mbSeries_sub_eq_sum` | MellinBarnesSeries: `mbSeries_tendsto` |
| MellinBarnesSeries: `mbSeries_tendsto` | MellinBarnesSeries: `mbSeries_hasSum` |
| MellinBarnesSeries: `mbSeries_hasSum` | MittagLefflerModulusRefutation: `source_barnes_identity` |
| MellinBarnesSeries: `mbSeries_Gamma_mul_eq_div` | MittagLefflerBarnesKernel: `kernel_eq_leftNumerator` |
| MellinBarnesSeries: `mbSeries_Gamma_residue` | MittagLefflerBarnesKernel: `leftNumerator_residue` |

The three literal numerator properties, horizontal limits and integrability
are used by the actual contour-data construction in `source_barnes_identity`.
`norm_line_le_recip_gamma` feeds `norm_integral_leftLine_le`, which feeds
`source_left_integral_tendsto_zero`, which is passed directly to the residue
HasSum theorem.

The right-strip numerator has the actual factorization at s=n+1 and residue
`1/(z^(n+1)*Gamma(beta-alpha*(n+1)))`. Its holomorphy uses entire reciprocal
Gamma, and no Gamma nonvanishing condition is added. The same horizontal
limits and line integrability supply `integral_right_step`, with right minus
left equal to two pi times the residue in dy normalization. The two steps
through one and two feed `source_endpoint_expansion`. Reciprocal Gamma at
minus one vanishes; the next coefficient is
`c_alpha = alpha*(alpha-1)*(alpha+1)/Gamma(2-alpha) > 0` for 1<alpha<2.

Principal-logarithm scaling gives `norm_kernel_pos_scale`, then the fixed-line
bound `norm_integral_pos_scale_le`. On the five-halves line this is a fixed
constant times r^(-5/2). Thus `source_endpoint_scaled_limit` gives
`r^2 E(alpha,alpha-1,r*w) -> c_alpha/w^2`. For
`eta=pi*(2-alpha)/4`, `t=tan(eta)` and `w=-1+i*t`, `ray_parameters`
proves the actual exterior margin and principal argument. The scaled negative
axis real part tends to c_alpha, while the ray norm tends to
`c_alpha/(1+t^2)`. The strict gap gives one finite positive radius in
`source_endpoint_failure`. The actual beta-continuity theorem then gives
`source_closed_beta_family`: one point is selected before beta and works for
every beta in the closed interval `[alpha-1,alpha-1+epsilon]`, with
`0<epsilon<1`, for every alpha in `(1,2)`.

The current source body of `result` consumes that family at alpha=3/2 and
beta=1/2, together with the original all-positive-alpha source existence and
unchanged complete `claim`. This is textual source consumption only; it does
not establish compiled liveness, axiom closure or admission. The inherited
finite certificate remains in the module but is no longer the result's source
proof path. The public theorem audit remains unfinished under issue
https://github.com/the-omega-institute/trureturing/issues/24571.

## Retirement at the repository pin

The consumer pins remain Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The DLMF source uses Lean
4.36.0-rc1 and Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca`;
this is a source port, not a dependency upgrade. Remove each port and use direct
imports when this repository's own pinned Mathlib supplies an equivalent
statement. No upstream acceptance event is a retirement condition.
