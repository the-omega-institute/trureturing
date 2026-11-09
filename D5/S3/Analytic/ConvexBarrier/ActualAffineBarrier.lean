import D5.S3.Analytic.ConvexBarrier.ActualRadialTensor
import Mathlib.LinearAlgebra.BilinearMap

/-! Actual affine restriction, metric, and symmetric projective cubic.
Zhang--Fu--Dai, arXiv:2611.06404v1, (3.17), (3.23), (3.24).
Uncompiled proof source. No invariance or derivative identity is a premise. -/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier.Actual

section AffineCalculus

variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def affineFunction (ν : ℝ) (F : E → ℝ) (b : E) (A : U →L[ℝ] E)
    (x : U) : ℝ := F (b+A x)/ν

theorem affine_hasFDerivAt (b : E) (A : U →L[ℝ] E) (x : U) :
    HasFDerivAt (fun y => b+A y) A x := by
  simpa using (hasFDerivAt_const b x).add A.hasFDerivAt

theorem affine_smooth {ν : ℝ} {F : E → ℝ} {b : E} {A : U →L[ℝ] E} {x : U}
    (hf : ContDiffAt ℝ 3 F (b+A x)) :
    ContDiffAt ℝ 3 (affineFunction ν F b A) x := by
  exact (hf.comp x ((contDiff_const.add A.contDiff).contDiffAt)).div_const ν

theorem affine_first {ν : ℝ} {F : E → ℝ} {b : E} {A : U →L[ℝ] E} {x : U}
    (hf : ContDiffAt ℝ 3 F (b+A x)) (u : U) :
    D1 (affineFunction ν F b A) x u = D1 F (b+A x) (A u)/ν := by
  have hd := ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp x
    (affine_hasFDerivAt b A x)).mul_const ν⁻¹
  have he : HasFDerivAt (affineFunction ν F b A)
      (ν⁻¹ • (D1 F (b+A x)).comp A) x := by
    simpa only [affineFunction,div_eq_mul_inv] using hd
  simpa [div_eq_mul_inv,mul_comm] using
    congrArg (fun L : U →L[ℝ] ℝ => L u) he.fderiv

theorem affine_second {ν : ℝ} {F : E → ℝ} {b : E} {A : U →L[ℝ] E} {x : U}
    (hf : ContDiffAt ℝ 3 F (b+A x)) (u v : U) :
    D2 (affineFunction ν F b A) x u v = D2 F (b+A x) (A u) (A v)/ν := by
  have he : (fun y => D1 (affineFunction ν F b A) y v) =ᶠ[𝓝 x]
      (fun y => D1 F (b+A y) (A v)/ν) := by
    filter_upwards [(affine_hasFDerivAt b A x).continuousAt.tendsto.eventually
      (hf.eventually (by norm_num))] with y hy
    exact affine_first hy v
  have hd := ((d1_hasFDerivAt hf (A v)).comp x (affine_hasFDerivAt b A x)).mul_const ν⁻¹
  have hl := d1_hasFDerivAt (affine_smooth hf (ν := ν)) v
  have hh := congrArg (fun L : U →L[ℝ] ℝ => L u)
    (hl.fderiv.symm.trans (he.fderiv_eq.trans (by
      simpa only [div_eq_mul_inv] using hd.fderiv)))
  simpa [div_eq_mul_inv,mul_comm] using hh

theorem affine_third {ν : ℝ} {F : E → ℝ} {b : E} {A : U →L[ℝ] E} {x : U}
    (hf : ContDiffAt ℝ 3 F (b+A x)) (u v w : U) :
    D3 (affineFunction ν F b A) x u v w = D3 F (b+A x) (A u) (A v) (A w)/ν := by
  have he : (fun y => D2 (affineFunction ν F b A) y v w) =ᶠ[𝓝 x]
      (fun y => D2 F (b+A y) (A v) (A w)/ν) := by
    filter_upwards [(affine_hasFDerivAt b A x).continuousAt.tendsto.eventually
      (hf.eventually (by norm_num))] with y hy
    exact affine_second hy v w
  have hd := ((d2_hasFDerivAt hf (A v) (A w)).comp x
    (affine_hasFDerivAt b A x)).mul_const ν⁻¹
  have hl := d2_hasFDerivAt (affine_smooth hf (ν := ν)) v w
  have hh := congrArg (fun L : U →L[ℝ] ℝ => L u)
    (hl.fderiv.symm.trans (he.fderiv_eq.trans (by
      simpa only [div_eq_mul_inv] using hd.fderiv)))
  simpa [div_eq_mul_inv,mul_comm] using hh

end AffineCalculus

section Tensors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def metricValue (f : E → ℝ) (x u v : E) : ℝ :=
  D2 f x u v - D1 f x u * D1 f x v

noncomputable def cubicValue (f : E → ℝ) (x u v w : E) : ℝ :=
  D3 f x u v w - 2*D1 f x u*D2 f x v w - 2*D1 f x v*D2 f x u w -
    2*D1 f x w*D2 f x u v + 4*D1 f x u*D1 f x v*D1 f x w

noncomputable def metric (f : E → ℝ) (x : E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (metricValue f x)
    (by intros; simp [metricValue,map_add]; ring)
    (by intros; simp [metricValue,map_smul,smul_eq_mul]; ring)
    (by intros; simp [metricValue,map_add]; ring)
    (by intros; simp [metricValue,map_smul,smul_eq_mul]; ring)

noncomputable def cubic (f : E → ℝ) (x : E) : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun u := LinearMap.mk₂ ℝ (cubicValue f x u)
    (by intros; simp [cubicValue,map_add]; ring)
    (by intros; simp [cubicValue,map_smul,smul_eq_mul]; ring)
    (by intros; simp [cubicValue,map_add]; ring)
    (by intros; simp [cubicValue,map_smul,smul_eq_mul]; ring)
  map_add' := by intros; ext v w; simp [cubicValue,map_add]; ring
  map_smul' := by intros; ext v w; simp [cubicValue,map_smul,smul_eq_mul]; ring

@[simp] theorem metric_apply (f : E → ℝ) (x u v : E) :
    metric f x u v = metricValue f x u v := rfl
@[simp] theorem cubic_apply (f : E → ℝ) (x u v w : E) :
    cubic f x u v w = cubicValue f x u v w := rfl

theorem metric_symm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (u v : E) :
    metric f x u v = metric f x v u := by
  simp only [metric_apply,metricValue,d2_symm hf u v]
  ring

theorem cubic_symm12 {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    cubic f x u v w = cubic f x v u w := by
  simp only [cubic_apply,cubicValue,d3_symm12 hf u v w,d2_symm hf u v]
  ring

theorem cubic_symm23 {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    cubic f x u v w = cubic f x u w v := by
  simp only [cubic_apply,cubicValue,d3_symm23 hf u v w,d2_symm hf v w]
  ring

end Tensors

noncomputable def sectionLinear : Base →L[ℝ] ScalarPoint :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (-ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
def sectionOrigin : ScalarPoint := ((0,1),0)
def sectionPoint (v : Base) : ScalarPoint := ((v.1,1-v.1),v.2)
def sectionDomain (c : ℝ) : Set Base := sectionPoint ⁻¹' coneInterior c

@[simp] theorem sectionLinear_apply (v : Base) :
    sectionLinear v = ((v.1,-v.1),v.2) := rfl
theorem sectionPoint_affine (v : Base) :
    sectionPoint v = sectionOrigin+sectionLinear v := by
  ext <;> simp [sectionPoint,sectionOrigin,sub_eq_add_neg]
theorem sectionPoint_continuous : Continuous sectionPoint := by
  unfold sectionPoint
  fun_prop

noncomputable def sectionFunction (ν : ℝ) (F : ScalarPoint → ℝ) : Base → ℝ :=
  affineFunction ν F sectionOrigin sectionLinear

theorem sectionFunction_apply (ν : ℝ) (F : ScalarPoint → ℝ) (v : Base) :
    sectionFunction ν F v = F (sectionPoint v)/ν := by
  rw [sectionPoint_affine]; rfl

/-- The actual logarithmically homogeneous extension of the affine base. -/
theorem section_extension {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) {s : ℝ} (hs : 0 < s) :
    F (s • sectionPoint v) = ν*(-Real.log s+sectionFunction ν F v) := by
  rw [hF.homogeneous _ hv s hs,sectionFunction_apply]
  field_simp [(parameter_pos hF).ne'] <;> ring

/-- Every point of the original cone is represented by this affine base.
No symmetry or larger domain enters the chart. -/
theorem section_reconstruction {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {x : ScalarPoint}
    (hx : x ∈ coneInterior c) :
    let s := x.1.1+x.1.2
    let v : Base := (x.1.1/s,x.2/s)
    v ∈ sectionDomain c ∧ F x = ν*(-Real.log s+sectionFunction ν F v) := by
  dsimp only
  let s := x.1.1+x.1.2
  let v : Base := (x.1.1/s,x.2/s)
  have hs : 0 < s := add_pos hx.1 hx.2.1
  have hscale : s • sectionPoint v = x := by
    ext <;> dsimp [sectionPoint,v,s]
    all_goals field_simp [hs.ne'] <;> ring
  have hnorm : sectionPoint v = (s⁻¹ • x.1,s⁻¹*x.2) := by
    ext <;> dsimp [sectionPoint,v,s]
    all_goals field_simp [hs.ne'] <;> ring
  have hv : v ∈ sectionDomain c := by
    change sectionPoint v ∈ coneInterior c
    rw [hnorm]
    exact (scalar_fiber_smul (inv_pos.mpr hs) ⟨hx.1,hx.2.1⟩ x.2).mpr hx
  refine ⟨hv,?_⟩
  rw [← hscale]
  exact section_extension hF hv hs

theorem section_smooth {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) : ContDiffAt ℝ 3 (sectionFunction ν F) v := by
  apply affine_smooth
  rw [← sectionPoint_affine]
  exact hF.smooth.contDiffAt (hF.domain_open.mem_nhds hv)

theorem section_first {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) :
    D1 (sectionFunction ν F) v h = a ν F (sectionPoint v) (sectionLinear h) := by
  have hf : ContDiffAt ℝ 3 F (sectionOrigin+sectionLinear v) := by
    rw [← sectionPoint_affine]
    exact hF.smooth.contDiffAt (hF.domain_open.mem_nhds hv)
  simpa only [sectionFunction,← sectionPoint_affine,a] using affine_first (ν := ν) hf h

theorem section_second {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (u w : Base) :
    D2 (sectionFunction ν F) v u w =
      D2 F (sectionPoint v) (sectionLinear u) (sectionLinear w)/ν := by
  have hf : ContDiffAt ℝ 3 F (sectionOrigin+sectionLinear v) := by
    rw [← sectionPoint_affine]
    exact hF.smooth.contDiffAt (hF.domain_open.mem_nhds hv)
  simpa only [sectionFunction,← sectionPoint_affine] using affine_second (ν := ν) hf u w

theorem section_third {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (u w z : Base) :
    D3 (sectionFunction ν F) v u w z =
      D3 F (sectionPoint v) (sectionLinear u) (sectionLinear w) (sectionLinear z)/ν := by
  have hf : ContDiffAt ℝ 3 F (sectionOrigin+sectionLinear v) := by
    rw [← sectionPoint_affine]
    exact hF.smooth.contDiffAt (hF.domain_open.mem_nhds hv)
  simpa only [sectionFunction,← sectionPoint_affine] using affine_third (ν := ν) hf u w z

theorem section_nonradial {v h : Base} (hh : h ≠ 0) (α : ℝ) :
    sectionLinear h ≠ α • sectionPoint v := by
  intro he
  have he1 := congrArg (fun p : ScalarPoint => p.1.1+p.1.2) he
  have ha : α = 0 := by
    change h.1 + -h.1 = α*v.1+α*(1-v.1) at he1
    nlinarith
  rw [ha,zero_smul] at he
  apply hh
  apply Prod.ext
  · exact congrArg (fun p : ScalarPoint => p.1.1) he
  · exact congrArg (fun p : ScalarPoint => p.2) he

theorem section_metric_Q {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) :
    metric (sectionFunction ν F) v h h = Q ν F (sectionPoint v) (sectionLinear h) := by
  simp only [metric_apply,metricValue,section_first hF hv,section_second hF hv,Q,b,pow_two]

theorem section_cubic_P {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) :
    cubic (sectionFunction ν F) v h h h = P ν F (sectionPoint v) (sectionLinear h) := by
  simp only [cubic_apply,cubicValue,section_first hF hv,section_second hF hv,
    section_third hF hv,P,t,b]
  ring

theorem section_radial_second {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) (α : ℝ) :
    diagonal 2 (coneInterior c) F (sectionPoint v) (α • sectionPoint v+sectionLinear h) =
      ν*((α-D1 (sectionFunction ν F) v h)^2+metric (sectionFunction ν F) v h h) := by
  rw [radial_second hF hv,section_first hF hv,section_metric_Q hF hv]

theorem section_radial_third {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) (α : ℝ) :
    diagonal 3 (coneInterior c) F (sectionPoint v) (α • sectionPoint v+sectionLinear h) =
      ν*(-2*(α-D1 (sectionFunction ν F) v h)^3 -
        6*(α-D1 (sectionFunction ν F) v h)*metric (sectionFunction ν F) v h h +
        cubic (sectionFunction ν F) v h h h) := by
  rw [radial_third hF hv,section_first hF hv,section_metric_Q hF hv,section_cubic_P hF hv]

theorem section_metric_pos {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (h : Base) (hh : h ≠ 0) :
    0 < metric (sectionFunction ν F) v h h := by
  rw [section_metric_Q hF hv]
  exact projective_pos hF hv _ (section_nonradial hh)

theorem section_cubic_bound {c ν s : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) {v : Base}
    (hv : v ∈ sectionDomain c) (hs : 1 ≤ s) (hν : ν = s^2+1) (h : Base) :
    |cubic (sectionFunction ν F) v h h h| ≤
      (2*(s^2-1)/s)*metric (sectionFunction ν F) v h h *
        Real.sqrt (metric (sectionFunction ν F) v h h) := by
  by_cases hh : h = 0
  · simp [hh]
  · rw [section_metric_Q hF hv,section_cubic_P hF hv]
    exact projective_cubic_bound hF hv _
      (projective_pos hF hv _ (section_nonradial hh)) hs hν

end D5.S3.Analytic.ConvexBarrier.Actual
