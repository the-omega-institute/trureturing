/- GID: D5/X_Frontier/GoldenWindowZeroObstruction
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normal-form obstruction and bare meromorphic point-test evasion. -/

import D5.X_Frontier.Hearts
import D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
import Mathlib.Tactic

/-! SEARCH RECEIPT (2026-09-03, pinned repository and pinned mathlib):
Repository searches for meromorphic continuation uniqueness found
`D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness.
meromorphic_continuation_unique`.  It proves pointwise uniqueness on an open
preconnected domain for `MeromorphicNFOn` representatives.

Pinned Mathlib searches in `Mathlib.Analysis.Meromorphic.Basic`,
`NormalForm`, and `Topology.Piecewise` found `MeromorphicAt.update`, which
preserves meromorphy under a single-point update, and
`continuousAt_update_same`, which detects the resulting discontinuity.  They
also found the normal-form upgrade
`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`, but no global
pointwise identity theorem for bare `MeromorphicOn`.

Consequently the obstruction theorem below quantifies only over candidates
that themselves carry `MeromorphicNFOn`; it does not refute the bare O-5
proposition.  The second theorem gives the precise reason: a bare meromorphic
representative can be changed at one point without changing its meromorphy or
agreement on the right sub-half-plane, while destroying analyticity at that
point. -/

/-! Frontier case: D5-T0018, the O-5 independence heart bound in
`D5.X_Frontier.Hearts`.  This module records normal-form obstruction results
toward that open heart -- it localizes the O-5 window obstruction under
normal-form candidates and exhibits the bare-meromorphic evasion -- but does
not close the heart. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex
open Filter

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

/-- An analytic zero off the structural line excludes candidates that carry
normal form on the continuation half-plane.  This is conditional: it neither
asserts that such a zero exists nor refutes the bare O-5 proposition. -/
theorem no_normal_form_o5_candidate_of_offline_analytic_zero
    (W : Complex -> Complex) (s₀ : Complex) (r : Real)
    (hr : 0 < r) (hr_lt : r < 1 / phi ^ 2)
    (hW_analytic : AnalyticOnNhd Complex W {s : Complex | r < s.re})
    (hW_agrees : forall s : Complex, 1 / phi ^ 2 < s.re -> W s = eulerGerm s)
    (hlo : 1 / (2 * phi ^ 3) < s₀.re) (hhi : s₀.re < 1 / phi ^ 2)
    (hr_s0 : r < s₀.re)
    (hzero : W s₀ = 0)
    (hoff : s₀.re ≠ structuralZero) :
    ¬ ∃ Zqc : Complex -> Complex,
      MeromorphicOn Zqc {s : Complex | 0 < s.re} ∧
      (forall s : Complex, 1 / phi ^ 2 < s.re -> Zqc s = eulerGerm s) ∧
      MeromorphicNFOn Zqc {s : Complex | r < s.re} ∧
      forall s : Complex, 1 / (2 * phi ^ 3) < s.re -> s.re < 1 / phi ^ 2 ->
        AnalyticAt Complex Zqc s -> Zqc s = 0 -> s.re = structuralZero := by
  rintro ⟨Zqc, hZqc_meromorphic, hZqc_agrees, hZqc_normal, hZqc_localizes⟩
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
    exact hr.trans hs
  have _hZqc_meromorphicΩ : MeromorphicOn Zqc Ω :=
    hZqc_meromorphic.mono_set hΩ_positive
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

/-- A single-point change produces a bare meromorphic representative that
keeps the right-half-plane agreement but is not analytic at the changed
point.  Thus an `AnalyticAt` guard cannot constrain arbitrary point values of
bare meromorphic representatives. -/
theorem bare_meromorphic_candidate_evades_zero_test
    (W : Complex -> Complex) (x : Complex) (r : Real)
    (hx : r < x.re) (hx_lt : x.re < 1 / phi ^ 2)
    (hW_analytic : AnalyticOnNhd Complex W {s : Complex | r < s.re})
    (hW_agrees : forall s : Complex, 1 / phi ^ 2 < s.re -> W s = eulerGerm s) :
    ∃ Zqc : Complex -> Complex,
      MeromorphicOn Zqc {s : Complex | r < s.re} ∧
      (forall s : Complex, 1 / phi ^ 2 < s.re -> Zqc s = eulerGerm s) ∧
      ¬ AnalyticAt Complex Zqc x := by
  classical
  refine ⟨Function.update W x (W x + 1), ?_, ?_, ?_⟩
  · intro s hs
    exact (hW_analytic s hs).meromorphicAt.update x (W x + 1)
  · intro s hs
    rw [Function.update_of_ne]
    · exact hW_agrees s hs
    · intro hsx
      subst s
      exact (lt_asymm hs hx_lt)
  · intro hanalytic
    have hupdated_limit : Tendsto W (nhdsWithin x {x}ᶜ) (nhds (W x + 1)) := by
      rw [← continuousAt_update_same]
      exact hanalytic.continuousAt
    have horiginal_limit : Tendsto W (nhdsWithin x {x}ᶜ) (nhds (W x)) :=
      (hW_analytic x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq : W x + 1 = W x :=
      tendsto_nhds_unique hupdated_limit horiginal_limit
    have heq' : W x + 1 = W x + 0 := heq.trans (add_zero (W x)).symm
    have hone : (1 : Complex) = 0 := add_left_cancel heq'
    exact one_ne_zero hone

#print axioms O5WindowLocalization
#print axioms no_normal_form_o5_candidate_of_offline_analytic_zero
#print axioms bare_meromorphic_candidate_evades_zero_test

end D5.X_Frontier.GoldenWindowZeroObstruction
