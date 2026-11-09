/- GID: D5/S3/Analytic/ConvexBarrier/ScalarEnvelope
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ScalarEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.ScalarMinimizerGraph
import D5.S3.Analytic.ConvexBarrier.HomogeneousHessian

/-! Envelope derivatives with only a C2 minimizer graph. In particular the
third derivative below does not differentiate that graph three times.
The cancellation argument is Zhang--Fu--Dai, Lemma 3.1, printed p. 6.
Uncompiled proof source. -/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier

noncomputable def minimizerLift {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u : Base) : ScalarPoint :=
  (u,fiberMinimizer hF u)

noncomputable def minimizerTangent {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u : Base) : Base →L[ℝ] ScalarPoint :=
  (ContinuousLinearMap.id ℝ Base).prod (fderiv ℝ (fiberMinimizer hF) u)

@[simp] theorem minimizerTangent_apply {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u h : Base) :
    minimizerTangent hF u h = (h,fderiv ℝ (fiberMinimizer hF) u h) := rfl

theorem minimizerLift_hasFDerivAt {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    HasFDerivAt (minimizerLift hF) (minimizerTangent hF u) u :=
  (hasFDerivAt_id u).prodMk
    ((fiberMinimizer_contDiffAt hF hu).differentiableAt (by norm_num)).hasFDerivAt

theorem minimizerLift_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    ContDiffOn ℝ 2 (minimizerLift hF) quadrant :=
  contDiffOn_id.prodMk (fiberMinimizer_smooth hF)

noncomputable def envelopeDerivative {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) (u : Base) : Base →L[ℝ] ℝ :=
  (fderiv ℝ F (minimizerLift hF u)).comp (ContinuousLinearMap.inl ℝ Base ℝ)

theorem partialMinimum_hasFDerivAt {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    HasFDerivAt (partialMinimum hF) (envelopeDerivative hF u) u := by
  have hp := (fiberMinimizer_spec hF hu).1
  have h := ((hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp)).differentiableAt
    (by norm_num)).hasFDerivAt.comp u (minimizerLift_hasFDerivAt hF hu)
  change HasFDerivAt (fun u => F (minimizerLift hF u)) (envelopeDerivative hF u) u
  convert h using 1
  rfl
  apply ContinuousLinearMap.ext
  intro v
  have hv : minimizerTangent hF u v =
      (v,(0:ℝ)) + (fderiv ℝ (fiberMinimizer hF) u v) • vertical := by
    simp [vertical]
  have hz := fiberMinimizer_stationary hF hu
  change fderiv ℝ F (minimizerLift hF u) (v,0) =
    fderiv ℝ F (minimizerLift hF u) (minimizerTangent hF u v)
  rw [hv,map_add,map_smul]
  change _ = _ + _ * fiberGradient F (u,fiberMinimizer hF u)
  rw [hz,mul_zero,add_zero]

theorem partialMinimum_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    ContDiffOn ℝ 3 (partialMinimum hF) quadrant := by
  have hd : ContDiffOn ℝ 2 (envelopeDerivative hF) quadrant := by
    apply ContDiffOn.clm_comp _ contDiffOn_const
    exact (hF.smooth.fderiv_of_isOpen hF.domain_open (by norm_num)).comp
      (minimizerLift_smooth hF) (fun u hu => (fiberMinimizer_spec hF hu).1)
  intro u hu
  apply ContDiffAt.contDiffWithinAt
  change ContDiffAt ℝ (↑(2 : ℕ) + 1) (partialMinimum hF) u
  rw [contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨envelopeDerivative hF,⟨quadrant,quadrant_isOpen.mem_nhds hu,?_⟩,
    hd.contDiffAt (quadrant_isOpen.mem_nhds hu)⟩
  exact fun v hv => partialMinimum_hasFDerivAt hF hv

theorem partialMinimum_first {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    fderiv ℝ (partialMinimum hF) u h =
      fderiv ℝ F (minimizerLift hF u) (h,0) := by
  exact congrArg (fun A : Base →L[ℝ] ℝ => A h)
    (partialMinimum_hasFDerivAt hF hu).fderiv

theorem minimizer_hessian_orthogonal {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    hessian F (minimizerLift hF u) (minimizerTangent hF u h) vertical = 0 := by
  have hp := (fiberMinimizer_spec hF hu).1
  have heq : (fun v => fiberGradient F (minimizerLift hF v)) =ᶠ[𝓝 u] (fun _ => 0) := by
    filter_upwards [quadrant_isOpen.mem_nhds hu] with v hv
    exact fiberMinimizer_stationary hF hv
  have hd := (fiberGradient_hasFDerivAt
    (hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp))).comp u
      (minimizerLift_hasFDerivAt hF hu)
  have he := congrArg (fun A : Base →L[ℝ] ℝ => A h) hd.fderiv
  have heq' : (fiberGradient F ∘ minimizerLift hF) =ᶠ[𝓝 u] (fun _ => 0) := by
    filter_upwards [heq] with v hv
    exact hv
  rw [heq'.fderiv_eq] at he
  simpa [hessian, minimizerLift] using he.symm

theorem minimizer_hessian_vertical_right {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) (a : ℝ) :
    hessian F (minimizerLift hF u) (minimizerTangent hF u h) (0,a) = 0 := by
  have he : ((0:Base),a) = a • vertical := by simp [vertical]
  rw [he,hessian,map_smul]
  change a * hessian F (minimizerLift hF u) (minimizerTangent hF u h) vertical = 0
  rw [minimizer_hessian_orthogonal hF hu,mul_zero]

theorem minimizer_hessian_vertical_left {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) (a : ℝ) :
    hessian F (minimizerLift hF u) (0,a) (minimizerTangent hF u h) = 0 := by
  have hs := (hF.smooth.contDiffAt
    (hF.domain_open.mem_nhds (fiberMinimizer_spec hF hu).1)).isSymmSndFDerivAt (by norm_num)
  unfold hessian
  change fderiv ℝ (fderiv ℝ F) (u, fiberMinimizer hF u) (0,a)
    (minimizerTangent hF u h) = 0
  rw [hs (0,a) (minimizerTangent hF u h)]
  exact minimizer_hessian_vertical_right hF hu h a

theorem partialMinimum_hessian {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h k : Base) :
    fderiv ℝ (fderiv ℝ (partialMinimum hF)) u h k =
      hessian F (minimizerLift hF u)
        (minimizerTangent hF u h) (minimizerTangent hF u k) := by
  have hp := (fiberMinimizer_spec hF hu).1
  have heq : (fun v => fderiv ℝ (partialMinimum hF) v k) =ᶠ[𝓝 u]
      (fun v => fderiv ℝ F (minimizerLift hF v) (k,0)) := by
    filter_upwards [quadrant_isOpen.mem_nhds hu] with v hv
    exact partialMinimum_first hF hv k
  have hdf := ((hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp)).fderiv_right
    (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hdf.hasFDerivAt.comp u (minimizerLift_hasFDerivAt hF hu)).clm_apply
    (hasFDerivAt_const (k,(0:ℝ)) u)
  have hdg := (((partialMinimum_smooth hF).contDiffAt (quadrant_isOpen.mem_nhds hu)).fderiv_right
    (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hl := hdg.hasFDerivAt.clm_apply (hasFDerivAt_const k u)
  have hdval := congrArg (fun A : Base →L[ℝ] ℝ => A h) hd.fderiv
  have hlval := congrArg (fun A : Base →L[ℝ] ℝ => A h) hl.fderiv
  rw [heq.fderiv_eq] at hlval
  have hh : fderiv ℝ (fderiv ℝ (partialMinimum hF)) u h k =
      hessian F (minimizerLift hF u) (minimizerTangent hF u h) (k,0) := by
    simpa [hessian, minimizerLift] using hlval.symm.trans hdval
  rw [hh]
  have hk : minimizerTangent hF u k = (k,(0:ℝ)) +
      (0,fderiv ℝ (fiberMinimizer hF) u k) := by simp
  simp only [hk,hessian,map_add]
  change _ = _ + hessian F (minimizerLift hF u) (minimizerTangent hF u h)
    (0,fderiv ℝ (fiberMinimizer hF) u k)
  rw [minimizer_hessian_vertical_right hF hu,add_zero]

theorem diagonal_three_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} (hD : IsOpen D) {F : E → ℝ} {p : E} (hp : p ∈ D)
    (_hf : ContDiffAt ℝ 3 F p) (v : E) :
    diagonal 3 D F p v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ F)) p v v v := by
  rw [diagonal,iteratedFDerivWithin_of_isOpen 3 hD hp,
    iteratedFDeriv_succ_apply_right,iteratedFDeriv_two_apply]
  rfl

theorem partialMinimum_second {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    diagonal 2 quadrant (partialMinimum hF) u h =
      diagonal 2 (coneInterior c) F (minimizerLift hF u) (minimizerTangent hF u h) := by
  have hp : minimizerLift hF u ∈ coneInterior c := by
    simpa [minimizerLift] using (fiberMinimizer_spec hF hu).1
  unfold diagonal
  rw [iteratedFDerivWithin_of_isOpen 2 quadrant_isOpen hu,
    iteratedFDerivWithin_of_isOpen 2 hF.domain_open hp,
    iteratedFDeriv_two_apply]
  rw [iteratedFDeriv_two_apply]
  simpa [hessian, minimizerLift] using partialMinimum_hessian hF hu h h

theorem partialMinimum_third {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    diagonal 3 quadrant (partialMinimum hF) u h =
      diagonal 3 (coneInterior c) F (minimizerLift hF u) (minimizerTangent hF u h) := by
  let z := fiberMinimizer hF
  let p := minimizerLift hF u
  let v := minimizerTangent hF u h
  let V : Base → ScalarPoint := fun y => (h,fderiv ℝ z y h)
  have hp : p ∈ coneInterior c := (fiberMinimizer_spec hF hu).1
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hp)
  have hg := (partialMinimum_smooth hF).contDiffAt (quadrant_isOpen.mem_nhds hu)
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ F)) p :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hz : DifferentiableAt ℝ (fderiv ℝ z) u :=
    ((fiberMinimizer_contDiffAt hF hu).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hV := (hasFDerivAt_const h u).prodMk
    (hz.hasFDerivAt.clm_apply (hasFDerivAt_const h u))
  have hX := minimizerLift_hasFDerivAt hF hu
  have hd := (((hH.hasFDerivAt.comp u hX).clm_apply hV).clm_apply hV)
  have heq : (fun y => fderiv ℝ (fderiv ℝ (partialMinimum hF)) y h h) =ᶠ[𝓝 u]
      (fun y => fderiv ℝ (fderiv ℝ F) (minimizerLift hF y) (V y) (V y)) := by
    filter_upwards [quadrant_isOpen.mem_nhds hu] with y hy
    exact partialMinimum_hessian hF hy h h
  have hgH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (partialMinimum hF))) u :=
    ((hg.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd := (hgH.hasFDerivAt.clm_apply (hasFDerivAt_const h u)).clm_apply
    (hasFDerivAt_const h u)
  have he := congrArg (fun A : Base →L[ℝ] ℝ => A h)
    (hgd.fderiv.symm.trans (heq.fderiv_eq.trans hd.fderiv))
  let a := fderiv ℝ (fderiv ℝ z) u h h
  have hr := minimizer_hessian_vertical_right hF hu h a
  have hl := minimizer_hessian_vertical_left hF hu h a
  rw [diagonal_three_eq quadrant_isOpen hu hg,
    diagonal_three_eq hF.domain_open hp hf]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,map_zero,zero_add,add_zero] at he
  change _ = hessian F p v (0,a) + (hessian F p (0,a) v + _) at he
  rw [hr,hl,zero_add,zero_add] at he
  exact he

end D5.S3.Analytic.ConvexBarrier
