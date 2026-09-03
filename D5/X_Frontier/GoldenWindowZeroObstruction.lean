/- GID: D5/X_Frontier/GoldenWindowZeroObstruction
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An off-line analytic zero obstructs normal-form O-5 window localization. -/

import D5.X_Frontier.Hearts
import D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
import Mathlib.Tactic

/-! SEARCH RECEIPT (2026-09-03, pinned repository and pinned mathlib):
Repository searches for meromorphic continuation uniqueness found
`D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness.
meromorphic_continuation_unique`.  It proves pointwise uniqueness on an open
preconnected domain for `MeromorphicNFOn` representatives.

Pinned Mathlib searches in `Mathlib.Analysis.Meromorphic.Basic`,
`IsolatedZeros`, `Order`, and `NormalForm` found the local identity theorem
`MeromorphicAt.frequently_eq_iff_eventuallyEq` and the normal-form upgrade
`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`, but no global
pointwise identity theorem for bare `MeromorphicOn`.  `NormalForm` explicitly
permits arbitrary changes on a codiscrete exceptional set and characterizes
normal form as fixing pole values to zero.  Thus bare `MeromorphicOn` cannot
transport the value `W s0 = 0` to an arbitrary continuation representative.

The theorem below therefore makes the permitted weakening explicit through
`hnormal`: every O-5 candidate under consideration must be in normal form on
the continuation half-plane.  The load-bearing equality is still derived by
meromorphic continuation uniqueness; it is not an assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex

namespace D5.X_Frontier.GoldenWindowZeroObstruction

open D5.X_Frontier.Hearts
open D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness

attribute [-instance] instCommCStarAlgebraComplex Complex.instRCLike

/-- The O-5 localization proposition, restated without importing its open
proof as a dependency. -/
def O5WindowLocalization : Prop :=
  ∃ Zqc : Complex -> Complex,
    MeromorphicOn Zqc {s : Complex | 0 < s.re} ∧
    (forall s : Complex, 1 / phi ^ 2 < s.re -> Zqc s = eulerGerm s) ∧
    forall s : Complex, 1 / (2 * phi ^ 3) < s.re -> s.re < 1 / phi ^ 2 ->
      AnalyticAt Complex Zqc s -> Zqc s = 0 -> s.re = structuralZero

/-- Under the explicit normal-form regularity premise, an analytic zero of a
continuation that lies off the structural line refutes O-5 window
localization.  This is conditional: it does not assert that such a zero
exists. -/
theorem o5_window_localization_fails_of_offline_analytic_zero
    (W : Complex -> Complex) (s₀ : Complex) (r : Real)
    (hr : 0 < r) (hr_lt : r < 1 / phi ^ 2)
    (hW_analytic : AnalyticOnNhd Complex W {s : Complex | r < s.re})
    (hW_agrees : forall s : Complex, 1 / phi ^ 2 < s.re -> W s = eulerGerm s)
    (hnormal : forall Zqc : Complex -> Complex,
      MeromorphicOn Zqc {s : Complex | r < s.re} ->
      (forall s : Complex, 1 / phi ^ 2 < s.re -> Zqc s = eulerGerm s) ->
      MeromorphicNFOn Zqc {s : Complex | r < s.re})
    (hlo : 1 / (2 * phi ^ 3) < s₀.re) (hhi : s₀.re < 1 / phi ^ 2)
    (hr_s0 : r < s₀.re)
    (hzero : W s₀ = 0)
    (hoff : s₀.re ≠ structuralZero) :
    ¬ O5WindowLocalization := by
  rintro ⟨Zqc, hZqc_meromorphic, hZqc_agrees, hZqc_localizes⟩
  let Ω : Set Complex := {s : Complex | r < s.re}
  let D : Set Complex := {s : Complex | 1 / phi ^ 2 < s.re}
  have hΩ_open : IsOpen Ω := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hΩ_preconnected : IsPreconnected Ω := by
    exact (convex_halfSpace_gt Complex.reLm.isLinear r).isPreconnected
  have hD_open : IsOpen D := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hD_nonempty : D.Nonempty := by
    refine ⟨((1 / phi ^ 2 + 1 : Real) : Complex), ?_⟩
    change 1 / phi ^ 2 < 1 / phi ^ 2 + 1
    linarith
  have hDΩ : D ⊆ Ω := by
    intro s hs
    change r < s.re
    change 1 / phi ^ 2 < s.re at hs
    exact hr_lt.trans hs
  have hΩ_positive : Ω ⊆ {s : Complex | 0 < s.re} := by
    intro s hs
    change 0 < s.re
    change r < s.re at hs
    exact hr.trans hs
  have hZqc_meromorphicΩ : MeromorphicOn Zqc Ω :=
    hZqc_meromorphic.mono_set hΩ_positive
  have hZqc_normal : MeromorphicNFOn Zqc Ω := by
    exact hnormal Zqc hZqc_meromorphicΩ hZqc_agrees
  have hW_normal : MeromorphicNFOn W Ω := by
    exact hW_analytic.meromorphicNFOn
  have hEqD : Set.EqOn Zqc W D := by
    intro s hs
    change 1 / phi ^ 2 < s.re at hs
    exact (hZqc_agrees s hs).trans (hW_agrees s hs).symm
  have hEqΩ : Set.EqOn Zqc W Ω :=
    meromorphic_continuation_unique hΩ_open hΩ_preconnected hD_open
      hD_nonempty hDΩ hZqc_normal hW_normal hEqD
  have hs₀Ω : s₀ ∈ Ω := hr_s0
  have hEq_nhds : Zqc =ᶠ[nhds s₀] W := by
    filter_upwards [hΩ_open.mem_nhds hs₀Ω] with s hs
    exact hEqΩ hs
  have hZqc_analytic : AnalyticAt Complex Zqc s₀ :=
    (analyticAt_congr hEq_nhds).2 (hW_analytic s₀ hs₀Ω)
  have hZqc_zero : Zqc s₀ = 0 := (hEqΩ hs₀Ω).trans hzero
  exact hoff (hZqc_localizes s₀ hlo hhi hZqc_analytic hZqc_zero)

#print axioms O5WindowLocalization
#print axioms o5_window_localization_fails_of_offline_analytic_zero

end D5.X_Frontier.GoldenWindowZeroObstruction
