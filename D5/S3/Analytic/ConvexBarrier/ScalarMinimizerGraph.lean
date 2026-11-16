/- GID: D5/S3/Analytic/ConvexBarrier/ScalarMinimizerGraph
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ScalarMinimizerGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.ScalarFiberMinimum
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! The attained minimizer graph is C2 by the pinned Mathlib implicit function
theorem. The stationary-point uniqueness lemma identifies the local branch
with the globally selected minimum. No regularity premise on that selection.
Zhang--Fu--Dai, Lemma 3.1; uncompiled proof source. -/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier

theorem fiberGradient_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    ContDiffOn ℝ 2 (fiberGradient F) (coneInterior c) :=
  (hF.smooth.fderiv_of_isOpen hF.domain_open (by norm_num)).clm_apply contDiffOn_const

/-- The vertical derivative block is a nonzero scalar operator. Its inverse
is constructed explicitly, instead of postulating invertibility. -/
theorem fiberGradient_vertical_invertible {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {p : ScalarPoint} (hp : p ∈ coneInterior c) :
    (fderiv ℝ (fiberGradient F) p ∘L ContinuousLinearMap.inr ℝ Base ℝ).IsInvertible := by
  let B := fderiv ℝ (fiberGradient F) p ∘L ContinuousLinearMap.inr ℝ Base ℝ
  let k := fiberHessian F p vertical vertical
  have hk : 0 < k := by
    change 0 < fiberHessian F p vertical vertical
    rw [← diagonal_two_eq_fiberHessian hF.domain_open hp vertical]
    exact hF.hessian_pos p hp vertical (by simp [vertical])
  have hB1 : B 1 = k := by
    dsimp [B,k]
    rw [(fiberGradient_hasFDerivAt
      (hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp))).fderiv]
    simp [fiberHessian, vertical]
  have hBx : ∀ x : ℝ, B x = x*k := by
    intro x
    have h := B.map_smul x (1:ℝ)
    simpa only [smul_eq_mul,mul_one,hB1] using h
  let C : ℝ →L[ℝ] ℝ := k⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := C)
  · apply ContinuousLinearMap.ext
    intro x
    change B (C x) = x
    rw [hBx]
    simp only [C,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp [hk.ne']
    <;> ring
  · apply ContinuousLinearMap.ext
    intro x
    change C (B x) = x
    rw [hBx]
    simp only [C,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp [hk.ne']
    <;> ring

theorem fiberMinimizer_contDiffAt {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    ContDiffAt ℝ 2 (fiberMinimizer hF) u := by
  let p : ScalarPoint := (u,fiberMinimizer hF u)
  have hp : p ∈ coneInterior c := (fiberMinimizer_spec hF hu).1
  have hg : ContDiffAt ℝ 2 (fiberGradient F) p :=
    (fiberGradient_smooth hF).contDiffAt (hF.domain_open.mem_nhds hp)
  have hi := fiberGradient_vertical_invertible hF hp
  let ψ := hg.implicitFunction (by norm_num) hi
  have hψ : ContDiffAt ℝ 2 ψ u := hg.contDiffAt_implicitFunction (by norm_num) hi
  have hψu : ψ u = fiberMinimizer hF u := hg.implicitFunction_apply_self (by norm_num) hi
  have hlift : Tendsto (fun v => (v,ψ v)) (𝓝 u) (𝓝 p) := by
    simpa only [p,hψu,id_eq] using (continuousAt_id.prodMk hψ.continuousAt).tendsto
  have hd : ∀ᶠ v in 𝓝 u, (v,ψ v) ∈ coneInterior c :=
    hlift.eventually (hF.domain_open.mem_nhds hp)
  have heq : ψ =ᶠ[𝓝 u] fiberMinimizer hF := by
    filter_upwards [hd,hg.eventually_apply_implicitFunction (by norm_num) hi] with v hv he
    apply stationary_eq_fiberMinimizer hF hv
    exact he.trans (fiberMinimizer_stationary hF hu)
  exact hψ.congr_of_eventuallyEq heq.symm

theorem fiberMinimizer_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    ContDiffOn ℝ 2 (fiberMinimizer hF) quadrant :=
  fun u hu => (fiberMinimizer_contDiffAt hF hu).contDiffWithinAt

noncomputable def partialMinimum {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u : Base) : ℝ :=
  F (u,fiberMinimizer hF u)

theorem fiberMinimizer_homogeneous {c ν t : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (ht : 0 < t) :
    fiberMinimizer hF (t • u) = t * fiberMinimizer hF u := by
  have htu : t • u ∈ quadrant := ⟨mul_pos ht hu.1,mul_pos ht hu.2⟩
  obtain ⟨hz,hm⟩ := fiberMinimizer_spec hF hu
  symm
  apply fiberMinimizer_unique hF htu ((scalar_fiber_smul ht hu _).mpr hz)
  intro w hw
  have hwt : (u,w/t) ∈ coneInterior c := by
    apply (scalar_fiber_smul ht hu (w/t)).mp
    simpa [mul_div_cancel₀ w ht.ne'] using hw
  have h1 := hF.homogeneous (u,fiberMinimizer hF u) hz t ht
  have h2 := hF.homogeneous (u,w/t) hwt t ht
  have hmin := hm (w/t) hwt
  simp only [Prod.smul_def,smul_eq_mul,mul_div_cancel₀ w ht.ne'] at h1 h2
  change F ((t * u.1, t * u.2), t * fiberMinimizer hF u) ≤
    F ((t * u.1, t * u.2), w)
  linarith

theorem partialMinimum_homogeneous {c ν t : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (ht : 0 < t) :
    partialMinimum hF (t • u) = partialMinimum hF u - ν * Real.log t := by
  unfold partialMinimum
  rw [fiberMinimizer_homogeneous hF hu ht]
  simpa only [Prod.smul_def,smul_eq_mul] using
    hF.homogeneous (u,fiberMinimizer hF u) (fiberMinimizer_spec hF hu).1 t ht

theorem partialMinimum_boundary_blowup {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : ScalarPoint → ℝ} (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {b : Base} (hb : b ∈ quadrantBoundary) (u : ℕ → Base)
    (hu : ∀ n, u n ∈ quadrant) (hlim : Tendsto u atTop (𝓝 b)) :
    Tendsto (partialMinimum hF ∘ u) atTop atTop := by
  exact hF.boundary_blowup (b,0) (quadrantBoundary_lift hc hc1 hb)
    (fun n => (u n,fiberMinimizer hF (u n)))
    (fun n => (fiberMinimizer_spec hF (hu n)).1)
    (feasible_lift_tendsto hc hc1 hb hlim
      (fun n => (fiberMinimizer_spec hF (hu n)).1))

end D5.S3.Analytic.ConvexBarrier
