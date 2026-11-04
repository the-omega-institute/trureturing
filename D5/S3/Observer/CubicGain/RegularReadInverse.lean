/- GID: D5/S3/Observer/CubicGain/RegularReadInverse
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/RegularReadInverse
   mirror-E: none(waiver:actual-original-read-local-inverse)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff]
   utility: none
   digest: An actual analytic inverse returns all eight original source coordinates with a local sup norm estimate. -/

import D5.S3.Observer.CubicGain.RegularReadJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-! An inverse of the actual original read pair, with the original eight-coordinate norm. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.RegularReadInverse

open D5.S3.Observer.CubicGain RegularParentChart RegularReadJacobian CommonWordSensitivity
open Metric Set
open scoped NNReal Topology

/-- The two actual reads whose local inverse is constructed. -/
def originalPM (W : OriginalWorld) : ℝ × ℝ :=
  ((originalResponse W).1,futureRead W [])

def sourceChart (W : OriginalWorld) : ℝ × ℝ := (W.1/W.2.1,W.2.1)

/-- All original parent worlds in the specified local chart and image neighborhood. -/
def localWorlds (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (A : Set (ℝ × ℝ)) : Set OriginalWorld :=
  {W | OriginalParent W ∧ 9005/10000 ≤ W.1 ∧ W.1 ≤ 9006/10000 ∧
    12758/100000 ≤ W.2.1 ∧ W.2.1 ≤ 12759/100000 ∧
    sourceChart W ∈ e.source ∧ originalPM W ∈ A}

private theorem world_chart (W : OriginalWorld) (hW : OriginalParent W)
    (hr : 9005/10000 ≤ W.1) (hr' : W.1 ≤ 9006/10000)
    (hb : 12758/100000 ≤ W.2.1) (hb' : W.2.1 ≤ 12759/100000) :
    W = chartWorld (sourceChart W) := by
  have hb0 : W.2.1 ≠ 0 := ne_of_gt hW.2.2.1
  have hm : (sourceChart W).1*(sourceChart W).2 = W.1 := div_mul_cancel₀ _ hb0
  have hc := analytic_original_parent_chart (sourceChart W)
    (by simpa only [hm] using hr) (by simpa only [hm] using hr') hb hb'
  exact hc.2.2.2.2.1 W hW hm.symm rfl

/-- A genuine analytic inverse of `(p,f_M)` returns the original source vector.
Its convex image ball has compact closure inside the inverse domain. The
source derivative is bounded on that closure, and its mean value estimate
uses the sup norm of all eight original coordinates. This is a local result;
no exhaustion or remote-branch assertion is included. -/
theorem actual_local_source_inverse (x : ℝ × ℝ)
    (hr : 9005/10000 ≤ x.1*x.2) (hr' : x.1*x.2 ≤ 9006/10000)
    (hb : 12758/100000 ≤ x.2) (hb' : x.2 ≤ 12759/100000) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ) (L : ℝ≥0),
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = chartRead ∧ x ∈ e.source ∧ 0 < ε ∧ 0 < (L:ℝ) ∧
      IsOpen (ball (chartRead x) ε) ∧ Convex ℝ (ball (chartRead x) ε) ∧
      IsCompact (closure (ball (chartRead x) ε)) ∧
      closure (ball (chartRead x) ε) ⊆ e.target ∧
      AnalyticOnNhd ℝ e.symm (closure (ball (chartRead x) ε)) ∧
      AnalyticOnNhd ℝ (fun q => chartSource (e.symm q))
        (closure (ball (chartRead x) ε)) ∧
      (∀ q ∈ closure (ball (chartRead x) ε),
        ‖fderiv ℝ (fun q => chartSource (e.symm q)) q‖ ≤ (L:ℝ)) ∧
      LipschitzOnWith L (fun q => chartSource (e.symm q)) (ball (chartRead x) ε) ∧
      chartWorld x ∈ localWorlds e (ball (chartRead x) ε) ∧
      (∀ W ∈ localWorlds e (ball (chartRead x) ε),
        chartSource (e.symm (originalPM W)) = sourceCoordinates W) ∧
      (∀ W ∈ localWorlds e (ball (chartRead x) ε),
        ∀ W' ∈ localWorlds e (ball (chartRead x) ε),
        ‖sourceCoordinates W-sourceCoordinates W'‖ ≤ (L:ℝ)*‖originalPM W-originalPM W'‖) := by
  obtain ⟨_,i,hi⟩ := actual_jacobian_nonsingular x hr hr' hb hb'
  have hc := analytic_original_parent_chart x hr hr' hb hb'
  have hread : AnalyticAt ℝ chartRead x := hc.2.2.2.1
  have hsource : AnalyticAt ℝ chartSource x := hc.2.2.1
  have hcd : ContDiffAt ℝ 1 chartRead x := hread.contDiffAt
  let e := hcd.toOpenPartialHomeomorph chartRead hi one_ne_zero
  have hx : x ∈ e.source := hcd.mem_toOpenPartialHomeomorph_source hi one_ne_zero
  have ht : chartRead x ∈ e.target := hcd.image_mem_toOpenPartialHomeomorph_target hi one_ne_zero
  have hec : e.symm (chartRead x) = x := e.left_inv hx
  have hinv : AnalyticAt ℝ e.symm (chartRead x) :=
    e.analyticAt_symm' hx hread hi.fderiv
  let H : (ℝ × ℝ) → (Fin 8 → ℝ) := fun q => chartSource (e.symm q)
  have hH : AnalyticAt ℝ H (chartRead x) := by
    have hs : AnalyticAt ℝ chartSource (e.symm (chartRead x)) := by rwa [hec]
    exact hs.comp hinv
  have hnhds : e.target ∩ {q | AnalyticAt ℝ e.symm q} ∩ {q | AnalyticAt ℝ H q}
      ∈ 𝓝 (chartRead x) :=
    Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds ht)
      hinv.eventually_analyticAt) hH.eventually_analyticAt
  obtain ⟨ε,hε,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  have hcl : closure (ball (chartRead x) ε) ⊆ closedBall (chartRead x) ε :=
    closure_ball_subset_closedBall
  have hcompact : IsCompact (closure (ball (chartRead x) ε)) :=
    (isCompact_closedBall (chartRead x) ε).of_isClosed_subset isClosed_closure hcl
  have hHOn : AnalyticOnNhd ℝ H (closure (ball (chartRead x) ε)) :=
    fun q hq => (hsub (hcl hq)).2
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hHOn.fderiv.continuousOn
  let L : ℝ≥0 := ⟨max 1 C,le_trans (by norm_num) (le_max_left _ _)⟩
  have hbound : ∀ q ∈ closure (ball (chartRead x) ε), ‖fderiv ℝ H q‖ ≤ (L:ℝ) :=
    fun q hq => (hC q hq).trans (le_max_right _ _)
  have hlip : LipschitzOnWith L H (ball (chartRead x) ε) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq => (hHOn q (subset_closure hq)).differentiableAt) _ (convex_ball _ _)
    intro q hq
    exact_mod_cast hbound q (subset_closure hq)
  have hchartcoords : sourceChart (chartWorld x) = x :=
    Prod.ext hc.2.2.2.2.2.2 rfl
  have hcenter : chartWorld x ∈ localWorlds e (ball (chartRead x) ε) := by
    refine ⟨hc.1,hr,hr',hb,hb',?_,?_⟩
    · rw [hchartcoords]
      exact hx
    · change chartRead x ∈ ball (chartRead x) ε
      exact mem_ball_self hε
  have hworld : ∀ W ∈ localWorlds e (ball (chartRead x) ε), H (originalPM W) = sourceCoordinates W := by
    intro W hW
    have heW := world_chart W hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2.1
    have hrW : originalPM W = chartRead (sourceChart W) := congrArg originalPM heW
    have hsW : sourceCoordinates W = chartSource (sourceChart W) := congrArg sourceCoordinates heW
    rw [hrW]
    change chartSource (e.symm (e (sourceChart W))) = sourceCoordinates W
    rw [e.left_inv hW.2.2.2.2.2.1]
    exact hsW.symm
  refine ⟨e,ε,L,rfl,hx,hε,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _),
    isOpen_ball,convex_ball _ _,hcompact,?_,?_,hHOn,hbound,hlip,hcenter,hworld,?_⟩
  · intro q hq
    exact (hsub (hcl hq)).1.1
  · intro q hq
    exact (hsub (hcl hq)).1.2
  · intro W hW W' hW'
    have h := hlip.dist_le_mul (originalPM W) hW.2.2.2.2.2.2
      (originalPM W') hW'.2.2.2.2.2.2
    rw [hworld W hW,hworld W' hW'] at h
    simpa only [dist_eq_norm] using h

#print axioms actual_local_source_inverse

end D5.S3.Observer.CubicGain.RegularReadInverse
