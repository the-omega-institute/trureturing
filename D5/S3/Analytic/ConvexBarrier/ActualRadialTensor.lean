/- GID: D5/S3/Analytic/ConvexBarrier/ActualRadialTensor
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ActualRadialTensor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.PartialMinimization
import D5.S3.Analytic.ConvexBarrier.PrimalDikin
import D5.S3.Analytic.ConvexBarrier.ScalarAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Actual Frechet tensors and radial identities. Mathematical source:
Zhang--Fu--Dai, arXiv:2611.06404v1, Lemmas 2.2, 3.3, 3.4 and Theorem 3.5.
This is uncompiled proof source, not a kernel or novelty claim.

The completed F1 and HomogeneousHessian sources both define the full name
`ConvexBarrier.hessian`. We import F1 and the noncolliding analytic primal
Dikin module, and give the generic radial calculation independent names.
No change to either completed input is required by this import closure.
-/

open Set Filter
open scoped Topology

namespace D5.S3.Analytic.ConvexBarrier.Actual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable abbrev D1 (F : E → ℝ) (x : E) := fderiv ℝ F x
noncomputable abbrev D2 (F : E → ℝ) (x : E) := fderiv ℝ (fderiv ℝ F) x
noncomputable abbrev D3 (F : E → ℝ) (x : E) :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x

theorem d1_hasFDerivAt {F : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 F x) (u : E) :
    HasFDerivAt (fun y => D1 F y u) ((D2 F x).flip u) x := by
  have h := (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  simpa using h.hasFDerivAt.clm_apply (hasFDerivAt_const u x)

theorem d2_hasFDerivAt {F : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 F x) (u v : E) :
    HasFDerivAt (fun y => D2 F y u v) (((D3 F x).flip u).flip v) x := by
  have h := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa using (h.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)

theorem d2_symm {F : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 F x) (u v : E) :
    D2 F x u v = D2 F x v u := hf.isSymmSndFDerivAt (by norm_num) u v

theorem d3_symm12 {F : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 F x) (u v w : E) :
    D3 F x u v w = D3 F x v u w := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num) u v)

theorem d3_symm23 {F : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 F x) (u v w : E) :
    D3 F x u v w = D3 F x u w v := by
  have he : (fun y => D2 F y v w) =ᶠ[𝓝 x] (fun y => D2 F y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact d2_symm hy v w
  have hh := (d2_hasFDerivAt hf v w).fderiv.symm.trans
    (he.fderiv_eq.trans (d2_hasFDerivAt hf w v).fderiv)
  exact congrArg (fun L : E →L[ℝ] ℝ => L u) hh

theorem diagonal_two {D : Set E} (hD : IsOpen D) {F : E → ℝ}
    {x : E} (hx : x ∈ D) (v : E) : diagonal 2 D F x v = D2 F x v v := by
  rw [diagonal, iteratedFDerivWithin_of_isOpen 2 hD hx, iteratedFDeriv_two_apply]

theorem diagonal_three {D : Set E} (hD : IsOpen D) {F : E → ℝ}
    {x : E} (hx : x ∈ D) (v : E) : diagonal 3 D F x v = D3 F x v v v := by
  rw [diagonal, iteratedFDerivWithin_of_isOpen 3 hD hx,
    iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

variable {ν : ℝ} {D B : Set E} {F : E → ℝ}

theorem parameter_pos (hF : IsLHSCB ν D B F) : 0 < ν :=
  lt_of_lt_of_le zero_lt_one hF.parameter

theorem euler (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) :
    D1 F x x = -ν := by
  have hf := (hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)).differentiableAt
    (by norm_num)
  have hl : HasDerivAt (fun t : ℝ => F (t • x)) (D1 F x x) 1 := by
    simpa [Function.comp_def, id_eq] using hf.hasFDerivAt.comp_hasDerivAt_of_eq 1
      ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
  have hr : HasDerivAt (fun t : ℝ => F x - ν * Real.log t) (-ν) 1 := by
    convert (hasDerivAt_const (1 : ℝ) (F x)).sub
      (((hasDerivAt_id (1 : ℝ)).log one_ne_zero).const_mul ν) using 1
    · funext t
      simp
    · norm_num
  have he : (fun t : ℝ => F (t • x)) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => F x - ν * Real.log t) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with t ht
    exact hF.homogeneous x hx t ht
  exact hl.unique (hr.congr_of_eventuallyEq he)

theorem hessian_euler (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (u : E) :
    D2 F x u x = -D1 F x u := by
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  have hd := (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hl := hd.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  have he : (fun y => D1 F y y) =ᶠ[𝓝 x] (fun _ => -ν) := by
    filter_upwards [hF.domain_open.mem_nhds hx] with y hy
    exact euler hF hy
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hl.unique ((hasFDerivAt_const (-ν) x).congr_of_eventuallyEq he))
  change D1 F x u + D2 F x u x = 0 at hh
  linarith

theorem radial_hessian (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (u : E) :
    D2 F x x x = ν ∧ D2 F x x u = -D1 F x u ∧ D2 F x u x = -D1 F x u := by
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  refine ⟨?_, ?_, hessian_euler hF hx u⟩
  · rw [hessian_euler hF hx, euler hF hx, neg_neg]
  · rw [d2_symm hf, hessian_euler hF hx]

/-- The radial cubic contraction is differentiated on the actual open domain. -/
theorem cubic_euler (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (u v : E) :
    D3 F x v u x = -2 * D2 F x u v := by
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  have hd := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_id x)
  have he : (fun y => D2 F y u y) =ᶠ[𝓝 x] (fun y => -D1 F y u) := by
    filter_upwards [hF.domain_open.mem_nhds hx] with y hy
    exact hessian_euler hF hy u
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v)
    (hl.unique ((d1_hasFDerivAt hf u).neg.congr_of_eventuallyEq he))
  have hh' : D2 F x u v + D3 F x v u x = -D2 F x v u := by
    simpa [D1, D2, D3, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_zero] using hh
  have hh := hh'
  rw [d2_symm hf v u] at hh
  linarith

theorem radial_cubic (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (u : E) :
    D3 F x x x x = -2*ν ∧
    D3 F x x x u = 2*D1 F x u ∧ D3 F x x u u = -2*D2 F x u u := by
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  refine ⟨?_, ?_, ?_⟩
  · rw [cubic_euler hF hx, (radial_hessian hF hx x).1]
  · rw [d3_symm23 hf x x u, cubic_euler hF hx, (radial_hessian hF hx u).2.2]
    ring
  · rw [d3_symm12 hf x u u, d3_symm23 hf u x u, cubic_euler hF hx]

noncomputable def a (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ := D1 F x h / ν
noncomputable def b (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ := D2 F x h h / ν
noncomputable def t (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ := D3 F x h h h / ν
noncomputable def Q (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ :=
  b ν F x h - a ν F x h ^ 2
noncomputable def P (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ :=
  t ν F x h - 6*b ν F x h*a ν F x h + 4*a ν F x h ^ 3

/-- Exact second derivative in every actual radial/transverse direction. -/
theorem radial_second (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) (α : ℝ) :
    diagonal 2 D F x (α • x + h) =
      ν*((α-a ν F x h)^2 + Q ν F x h) := by
  obtain ⟨hxx,hxh,hhx⟩ := radial_hessian hF hx h
  rw [diagonal_two hF.domain_open hx]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hxx, hxh, hhx]
  unfold Q b a
  field_simp [(parameter_pos hF).ne'] <;> ring

/-- Exact third derivative; C3 symmetry was proved above, not postulated. -/
theorem radial_third (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) (α : ℝ) :
    diagonal 3 D F x (α • x + h) =
      ν*(-2*(α-a ν F x h)^3 - 6*(α-a ν F x h)*Q ν F x h + P ν F x h) := by
  have hf := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  obtain ⟨hxxx,hxxh,hxhh⟩ := radial_cubic hF hx h
  have hxhx := (d3_symm23 hf x h x).trans hxxh
  have hhxx := (d3_symm12 hf h x x).trans hxhx
  have hhxh := (d3_symm12 hf h x h).trans hxhh
  have hhhx := (d3_symm23 hf h h x).trans hhxh
  rw [diagonal_three hF.domain_open hx]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    hxxx,hxxh,hxhh,hxhx,hhxx,hhxh,hhhx]
  unfold P Q t b a
  field_simp [(parameter_pos hF).ne'] <;> ring

theorem projective_pos (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E)
    (hn : ∀ α : ℝ, h ≠ α • x) : 0 < Q ν F x h := by
  have hv : a ν F x h • x + h ≠ 0 := by
    intro he
    apply hn (-a ν F x h)
    have : h = -(a ν F x h • x) := by
      calc
        h = (a ν F x h • x+h)-a ν F x h • x := by abel
        _ = -(a ν F x h • x) := by rw [he,zero_sub]
    simpa using this
  have hp := hF.hessian_pos x hx _ hv
  rw [radial_second hF hx, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add] at hp
  exact (mul_pos_iff_of_pos_left (parameter_pos hF)).mp hp

/-- Squared SC after actual radial substitution and positive normalization. -/
theorem normalized_sc (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E)
    (hq : 0 < Q ν F x h) (u : ℝ) :
    (-2*u^3-6*u+P ν F x h/(Q ν F x h*Real.sqrt (Q ν F x h)))^2 ≤
      4*ν*(u^2+1)^3 := by
  let q := Q ν F x h
  let v := Real.sqrt q
  have hv : 0 < v := Real.sqrt_pos.mpr hq
  have hv2 : v^2 = q := Real.sq_sqrt hq.le
  have hs := hF.self_concordant x hx ((a ν F x h+u*v) • x+h)
  rw [radial_second hF hx, radial_third hF hx] at hs
  have hp : 0 ≤ ν*((a ν F x h+u*v-a ν F x h)^2+q) := by
    have := parameter_pos hF
    positivity
  have hs2 := mul_self_le_mul_self (abs_nonneg _) hs
  simp only [← pow_two,sq_abs] at hs2
  have hr := Real.sq_sqrt hp
  have hn := parameter_pos hF
  have he1 : (a ν F x h+u*v-a ν F x h)^2+q = q*(u^2+1) := by
    calc
      _ = u^2*v^2+q := by ring
      _ = _ := by rw [hv2]; ring
  have he2 : -2*(a ν F x h+u*v-a ν F x h)^3-
      6*(a ν F x h+u*v-a ν F x h)*q+P ν F x h =
      q*v*(-2*u^3-6*u+P ν F x h/(q*v)) := by
    have hc : q*v*(P ν F x h/(q*v)) = P ν F x h :=
      mul_div_cancel₀ _ (mul_ne_zero hq.ne' hv.ne')
    calc
      _ = (-2*u^3*v)*(v^2-q)+q*v*(-2*u^3-6*u)+P ν F x h := by ring
      _ = q*v*(-2*u^3-6*u)+P ν F x h := by rw [hv2,sub_self,mul_zero,zero_add]
      _ = _ := by rw [mul_add,hc]
  change (ν*(-2*(a ν F x h+u*v-a ν F x h)^3-
      6*(a ν F x h+u*v-a ν F x h)*q+P ν F x h))^2 ≤ _ at hs2
  rw [he2] at hs2
  have he3 : (2*(ν*((a ν F x h+u*v-a ν F x h)^2+q))*
      Real.sqrt (ν*((a ν F x h+u*v-a ν F x h)^2+q)))^2 =
      4*ν^3*q^3*(u^2+1)^3 := by
    calc
      _ = 4*(ν*((a ν F x h+u*v-a ν F x h)^2+q))^2 *
          (Real.sqrt (ν*((a ν F x h+u*v-a ν F x h)^2+q)))^2 := by ring
      _ = _ := by rw [hr,he1]; ring
  change _ ≤ (2*(ν*((a ν F x h+u*v-a ν F x h)^2+q))*
      Real.sqrt (ν*((a ν F x h+u*v-a ν F x h)^2+q)))^2 at hs2
  rw [he3] at hs2
  have hc : 0 < ν^2*q^3 := by positivity
  have hL : (ν*(q*v*(-2*u^3-6*u+P ν F x h/(q*v))))^2 =
      (ν^2*q^3)*(-2*u^3-6*u+P ν F x h/(q*v))^2 := by
    calc
      _ = ν^2*q^2*v^2*(-2*u^3-6*u+P ν F x h/(q*v))^2 := by ring
      _ = _ := by rw [hv2]; ring
  rw [hL] at hs2
  apply (le_of_mul_le_mul_left ?_ hc)
  convert hs2 using 1 <;> ring

/-- A nonradial positive projective direction already forces nu >= 2.
This uses SC at u=±1, independently of duality or chord assumptions. -/
theorem parameter_two (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E)
    (hq : 0 < Q ν F x h) : 2 ≤ ν := by
  have hp := normalized_sc hF hx h hq 1
  have hm := normalized_sc hF hx h hq (-1)
  norm_num at hp hm
  nlinarith [sq_nonneg (P ν F x h/(Q ν F x h*Real.sqrt (Q ν F x h)))]

theorem projective_cubic_bound (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D)
    (h : E) (hq : 0 < Q ν F x h) {s : ℝ} (hs : 1 ≤ s) (hν : ν = s^2+1) :
    |P ν F x h| ≤ (2*(s^2-1)/s)*Q ν F x h*Real.sqrt (Q ν F x h) := by
  have hb := sharp_projective_cubic hs (fun u => by
    simpa only [← hν] using normalized_sc hF hx h hq u)
  rw [abs_div, abs_of_pos (mul_pos hq (Real.sqrt_pos.mpr hq))] at hb
  simpa only [mul_assoc] using
    (div_le_iff₀ (mul_pos hq (Real.sqrt_pos.mpr hq))).mp hb

/-- Actual primal endpoint polynomial, adapted from the completed primal
calculus under fresh names to avoid F1's `hessian` declaration collision. -/
theorem primal_polynomial (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D)
    (h : E) (δ lam : ℝ) :
    diagonal 2 D F x (lam • (x+δ • h)-x) =
      primalQuadratic ν (1-a ν F x h*δ) (Q ν F x h*δ^2) lam := by
  obtain ⟨hxx,hxh,hhx⟩ := radial_hessian hF hx h
  have hv : lam • (x+δ • h)-x = (lam-1) • x+(lam*δ) • h := by
    rw [smul_add,smul_smul,sub_smul,one_smul]
    abel
  rw [diagonal_two hF.domain_open hx, hv]
  simp only [map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,hxx,hxh,hhx]
  unfold primalQuadratic Q b a
  field_simp [(parameter_pos hF).ne'] <;> ring

end D5.S3.Analytic.ConvexBarrier.Actual
