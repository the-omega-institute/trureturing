/- GID: D5/S3/Analytic/ConvexBarrier/ScalarFiberMinimum
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ScalarFiberMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Geometry.PowerCone.PartialProjection
import D5.S3.Analytic.ConvexBarrier.IntervalMinimum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Attainment and uniqueness from the original arbitrary barrier.
No evenness, explicit barrier formula, compact fiber, or attainment premise.
Zhang--Fu--Dai, arXiv:2611.06404v1, Theorem 3.5, printed p. 9.
Uncompiled proof source. -/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier

abbrev Base := ℝ × ℝ
abbrev ScalarPoint := Point ℝ

def fiber (F : ScalarPoint → ℝ) (u : Base) (z : ℝ) : ℝ := F (u,z)
def vertical : ScalarPoint := (0,1)
noncomputable def fiberGradient (F : ScalarPoint → ℝ) (p : ScalarPoint) : ℝ :=
  fderiv ℝ F p vertical
noncomputable def fiberHessian (F : ScalarPoint → ℝ) (p v w : ScalarPoint) : ℝ :=
  fderiv ℝ (fderiv ℝ F) p v w

theorem diagonal_two_eq_fiberHessian {D : Set ScalarPoint} (hD : IsOpen D)
    {F : ScalarPoint → ℝ} {p : ScalarPoint} (hp : p ∈ D) (v : ScalarPoint) :
    diagonal 2 D F p v = fiberHessian F p v v := by
  rw [diagonal,iteratedFDerivWithin_of_isOpen 2 hD hp,iteratedFDeriv_two_apply]
  rfl

theorem fiber_hasDerivAt {F : ScalarPoint → ℝ} {u : Base} {z : ℝ}
    (hf : DifferentiableAt ℝ F (u,z)) :
    HasDerivAt (fiber F u) (fiberGradient F (u,z)) z := by
  exact hf.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))

theorem fiberGradient_hasFDerivAt {F : ScalarPoint → ℝ} {p : ScalarPoint}
    (hf : ContDiffAt ℝ 3 F p) :
    @HasFDerivAt ℝ _ ScalarPoint
      (Prod.normedAddCommGroup (E := ℝ × ℝ) (F := ℝ)).toAddCommGroup
      (Prod.normedSpace (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ)).toModule
      (Prod.normedAddCommGroup (E := ℝ × ℝ) (F := ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fiberGradient F) ((fderiv ℝ (fderiv ℝ F) p).flip vertical) p := by
  change @HasFDerivAt ℝ _ ScalarPoint
      (Prod.normedAddCommGroup (E := ℝ × ℝ) (F := ℝ)).toAddCommGroup
      (Prod.normedSpace (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ)).toModule
      (Prod.normedAddCommGroup (E := ℝ × ℝ) (F := ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun y => (fderiv ℝ F y) vertical)
      ((fderiv ℝ (fderiv ℝ F) p).flip vertical) p
  have hdf : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  simpa [fiberGradient] using
    hdf.hasFDerivAt.clm_apply (hasFDerivAt_const vertical p)

theorem fiber_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    ContDiffOn ℝ 3 (fiber F u) (Ioo (-weight c u.1 u.2) (weight c u.1 u.2)) := by
  apply hF.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
  intro z hz
  exact ((scalar_mem_fiber_iff hu _).mpr hz)

theorem fiber_deriv_eq {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} {z : ℝ} (hp : (u,z) ∈ coneInterior c) :
    deriv (fiber F u) z = fiberGradient F (u,z) := by
  exact (fiber_hasDerivAt ((hF.smooth.contDiffAt
    (hF.domain_open.mem_nhds hp)).differentiableAt (by norm_num))).deriv

theorem fiber_second_deriv {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} {z : ℝ} (hp : (u,z) ∈ coneInterior c) :
    deriv (deriv (fiber F u)) z = fiberHessian F (u,z) vertical vertical := by
  have hu : u ∈ quadrant := ⟨hp.1,hp.2.1⟩
  have hz : z ∈ Ioo (-weight c u.1 u.2) (weight c u.1 u.2) :=
    (scalar_mem_fiber_iff hu _).mp hp
  have he : deriv (fiber F u) =ᶠ[𝓝 z] (fun z => fiberGradient F (u,z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
    exact fiber_deriv_eq hF ((scalar_mem_fiber_iff hu _).mpr hy)
  rw [he.deriv_eq]
  exact ((fiberGradient_hasFDerivAt
    (hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp))).comp_hasDerivAt z
      ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))).deriv

theorem fiber_second_pos {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} {z : ℝ} (hp : (u,z) ∈ coneInterior c) :
    0 < (deriv^[2] (fiber F u)) z := by
  have hp' := hF.hessian_pos (u,z) hp vertical (by simp [vertical])
  rw [diagonal_two_eq_fiberHessian hF.domain_open hp vertical] at hp'
  simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,
    Function.iterate_one,fiber_second_deriv hF hp] using hp'

/-- Every finite fiber sublevel is compact, although the fiber is an open interval. -/
theorem fiber_sublevel_isCompact {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (M : ℝ) :
    IsCompact {z : ℝ | (u,z) ∈ coneInterior c ∧ F (u,z) ≤ M} := by
  have he := scalar_fiber_endpoints_boundary (c := c) hu
  have h := interval_sublevel_isCompact (fiber_smooth hF hu).continuousOn
    (fun v hv hlim => hF.boundary_blowup _ he.1 (fun n => (u,v n))
      (fun n => (scalar_mem_fiber_iff hu _).mpr (hv n))
      (tendsto_const_nhds.prodMk_nhds hlim))
    (fun v hv hlim => hF.boundary_blowup _ he.2 (fun n => (u,v n))
      (fun n => (scalar_mem_fiber_iff hu _).mpr (hv n))
      (tendsto_const_nhds.prodMk_nhds hlim)) M
  simpa only [← scalar_fiber_eq hu,mem_setOf_eq,fiber] using h

theorem fiber_exists_unique_min {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    ∃! z : ℝ, (u,z) ∈ coneInterior c ∧
      ∀ w : ℝ, (u,w) ∈ coneInterior c → F (u,z) ≤ F (u,w) := by
  have hw := weight_pos (c := c) hu
  have he := scalar_fiber_endpoints_boundary (c := c) hu
  have h := interval_exists_unique_min
    (show (0:ℝ) ∈ Ioo (-weight c u.1 u.2) (weight c u.1 u.2) by
      exact ⟨by linarith,hw⟩)
    (fiber_smooth hF hu).continuousOn
    (fun z hz => fiber_second_pos hF ((scalar_mem_fiber_iff hu _).mpr hz))
    (fun v hv hlim => hF.boundary_blowup _ he.1 (fun n => (u,v n))
      (fun n => (scalar_mem_fiber_iff hu _).mpr (hv n))
      (tendsto_const_nhds.prodMk_nhds hlim))
    (fun v hv hlim => hF.boundary_blowup _ he.2 (fun n => (u,v n))
      (fun n => (scalar_mem_fiber_iff hu _).mpr (hv n))
      (tendsto_const_nhds.prodMk_nhds hlim))
  simpa only [← scalar_fiber_eq hu,mem_setOf_eq,isMinOn_iff,fiber] using h

noncomputable def fiberMinimizer {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u : Base) : ℝ :=
  by
  classical
  exact if hu : u ∈ quadrant then
    Classical.choose (fiber_exists_unique_min hF hu).exists else 0

theorem fiberMinimizer_spec {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    (u,fiberMinimizer hF u) ∈ coneInterior c ∧
      ∀ w : ℝ, (u,w) ∈ coneInterior c → F (u,fiberMinimizer hF u) ≤ F (u,w) := by
  simpa only [fiberMinimizer,dif_pos hu] using
    Classical.choose_spec (fiber_exists_unique_min hF hu).exists

theorem fiberMinimizer_unique {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) {z : ℝ}
    (hz : (u,z) ∈ coneInterior c)
    (hm : ∀ w : ℝ, (u,w) ∈ coneInterior c → F (u,z) ≤ F (u,w)) :
    z = fiberMinimizer hF u :=
  (fiber_exists_unique_min hF hu).unique ⟨hz,hm⟩ (fiberMinimizer_spec hF hu)

theorem fiberMinimizer_stationary {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    fiberGradient F (u,fiberMinimizer hF u) = 0 := by
  obtain ⟨hp,hm⟩ := fiberMinimizer_spec hF hu
  rw [← fiber_deriv_eq hF hp]
  exact interval_min_stationary ((scalar_mem_fiber_iff hu _).mp hp)
    (fun w hw => hm w ((scalar_mem_fiber_iff hu _).mpr hw))

/-- A stationary fiber point is the chosen minimizer; this identifies each local
implicit branch with the globally attained choice. -/
theorem stationary_eq_fiberMinimizer {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} {z : ℝ} (hz : (u,z) ∈ coneInterior c)
    (hzero : fiberGradient F (u,z) = 0) : z = fiberMinimizer hF u := by
  have hu : u ∈ quadrant := ⟨hz.1,hz.2.1⟩
  let I := Ioo (-weight c u.1 u.2) (weight c u.1 u.2)
  have hd : ContinuousOn (deriv (fiber F u)) I := by
    have h := (fiber_smooth hF hu).fderiv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
    have h' := h.clm_apply (g := fun _ => (1:ℝ)) contDiffOn_const
    simpa only [fderiv_apply_one_eq_deriv] using h'.continuousOn
  have hmono : StrictMonoOn (deriv (fiber F u)) I :=
    strictMonoOn_of_deriv_pos (convex_Ioo (-weight c u.1 u.2) (weight c u.1 u.2)) hd (by
      intro y hy
      have hy' : y ∈ I := by simpa [I] using hy
      simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,
        Function.iterate_one] using fiber_second_pos hF ((scalar_mem_fiber_iff hu _).mpr hy'))
  apply hmono.injOn ((scalar_mem_fiber_iff hu _).mp hz)
    ((scalar_mem_fiber_iff hu _).mp (fiberMinimizer_spec hF hu).1)
  rw [fiber_deriv_eq hF hz,hzero,
    fiber_deriv_eq hF (fiberMinimizer_spec hF hu).1,fiberMinimizer_stationary hF hu]

end D5.S3.Analytic.ConvexBarrier
