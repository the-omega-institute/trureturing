/- GID: D5/S3/Analytic/PowerSeries/PositiveParameterClosedSubmodule
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive values of an analytic curve determine its coefficients in a closed submodule. -/
/-
SPDX-License-Identifier: Apache-2.0
Independent source proposal, 2026-10-26.

Fixed Mathlib searched: 56a005855ea17e0b0958f73ec801ae140b0a1679.
No exact coefficient-in-closed-submodule theorem was found in the searched
repository D5 and Mathlib analytic/calculus/quotient APIs. This proof reuses
Mathlib's quotient map, linear images of power series, isolated-zero theorem,
and power-series uniqueness. No completeness assumption is needed here.

Intended actual consumer: in the fourth weighted Gaussian coefficient space,
take f(t) = B_(sqrt t) / (2 * (1-t)^(9/4)) and
K = closure(span { B_q : 0 < q < delta }). The source normalization is
f(t) = sum_(k>=1) t^k / N_(2k) * (e_k - z_k * e_0).
The theorem below extracts those exact coefficient directions from positive
values only; neither their membership in K nor density is a hypothesis.
Constant coefficient is included, without assuming f(0)=0.

No compilation or official-acceptance claim is made by this source.
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.DenselyOrdered

/-! Coefficient extraction from positive parameter values in a closed submodule. -/

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped Topology

namespace RHGaussianDilationCore

/-- A closed real submodule containing an analytic curve at all sufficiently
small positive parameters contains every coefficient of its series at zero.
The hypothesis is genuinely one-sided; f need not take values in K at negative
parameters. The conclusion includes the constant coefficient. -/
theorem powerSeries_coeff_mem_of_positive_values
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : FormalMultilinearSeries ℝ ℝ E}
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E))
    (hp : HasFPowerSeriesAt f p 0)
    {r : ℝ} (hr : 0 < r)
    (hvalues : ∀ t : ℝ, 0 < t → t < r → f t ∈ K)
    (n : ℕ) : p.coeff n ∈ K := by
  letI : IsClosed (K : Set E) := hK
  have hquotient :
      HasFPowerSeriesAt (K.mkQL ∘ f) (K.mkQL.compFormalMultilinearSeries p) 0 := by
    obtain ⟨R, hR⟩ := hp
    exact (K.mkQL.comp_hasFPowerSeriesOnBall hR).hasFPowerSeriesAt
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), (K.mkQL ∘ f) t = 0 := by
    have hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r :=
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hupper] with t ht htr
    change (Submodule.Quotient.mk (f t) : E ⧸ K) = 0
    exact (Submodule.Quotient.mk_eq_zero K).mpr (hvalues t ht htr)
  have hfrequent : ∃ᶠ t in 𝓝[≠] (0 : ℝ), (K.mkQL ∘ f) t = 0 :=
    hright.frequently.filter_mono (nhdsGT_le_nhdsNE 0)
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), (K.mkQL ∘ f) t = 0 :=
    hquotient.analyticAt.frequently_zero_iff_eventually_zero.mp hfrequent
  have hseries : K.mkQL.compFormalMultilinearSeries p = 0 :=
    hquotient.eq_zero_of_eventually hlocal
  have hcoefficient : K.mkQL (p.coeff n) = 0 := by
    have h := congrArg
      (fun q : FormalMultilinearSeries ℝ ℝ (E ⧸ K) => q n 1) hseries
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
      FormalMultilinearSeries.coeff, FormalMultilinearSeries.zero_apply,
      ContinuousMultilinearMap.zero_apply] using h
  change (Submodule.Quotient.mk (p.coeff n) : E ⧸ K) = 0 at hcoefficient
  exact (Submodule.Quotient.mk_eq_zero K).mp hcoefficient

end RHGaussianDilationCore
