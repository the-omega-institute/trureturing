/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondShearObstruction4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Ricci-flat point-cone screens and the Weyl-shear obstruction. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.PerturbedCausalOrderWeyl4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernelHS
import D5.S3.Analysis.ScreenAnisotropy
import D5.S3.Analysis.PlanarKernelSingularity
import D5.S3.Analysis.L2ProductKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact pre-caustic point-cone screen forms for a four-dimensional Ricci-flat plane wave. -/

compile_only_with_mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace NullConeGravity
open Real Set MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace

/-- Oscillatory Rosen factor with point-cone initial conditions. -/
def rosenP (α u : ℝ) : ℝ := sin (α * u) / α

/-- Hyperbolic Rosen factor with point-cone initial conditions. -/
def rosenQ (α u : ℝ) : ℝ := sinh (α * u) / α

private theorem hasDerivAt_linear (α u : ℝ) : HasDerivAt (fun w : ℝ => α * w) α u := by
  simpa using (hasDerivAt_id u).const_mul α

/-- The two diagonal factors of the existing vertex Jacobi propagator. -/
theorem rosen_vertex_jacobian (α u : ℝ) :
    D5.S3.Geometry.Lorentz.PerturbedCausalOrderWeyl4D.vertexJacobian α u =
      Matrix.diagonal ![rosenQ α u, rosenP α u] := rfl

/-- The oscillatory factor and its velocity solve the Jacobi equation. -/
theorem rosenP_jacobi {α : ℝ} (hα : 0 < α) (u : ℝ) :
    HasDerivAt (rosenP α) (cos (α * u)) u ∧
      HasDerivAt (fun w => cos (α * w)) (-(α ^ 2) * rosenP α u) u := by
  constructor
  · unfold rosenP
    convert (hasDerivAt_linear α u).sin.div_const α using 1
    field_simp
  · convert (hasDerivAt_linear α u).cos using 1
    unfold rosenP
    field_simp

/-- The hyperbolic factor and its velocity solve the Jacobi equation. -/
theorem rosenQ_jacobi {α : ℝ} (hα : 0 < α) (u : ℝ) :
    HasDerivAt (rosenQ α) (cosh (α * u)) u ∧
      HasDerivAt (fun w => cosh (α * w)) (α ^ 2 * rosenQ α u) u := by
  constructor
  · unfold rosenQ
    convert (hasDerivAt_linear α u).sinh.div_const α using 1
    field_simp
  · convert (hasDerivAt_linear α u).cosh using 1
    unfold rosenQ
    field_simp

/-- Both factors vanish at the tip with unit affine velocity. -/
theorem rosen_tip_initial_conditions {α : ℝ} (hα : 0 < α) :
    rosenP α 0 = 0 ∧ rosenQ α 0 = 0 ∧
      HasDerivAt (rosenP α) 1 0 ∧ HasDerivAt (rosenQ α) 1 0 := by
  refine ⟨by simp [rosenP], by simp [rosenQ], ?_, ?_⟩
  · simpa using (rosenP_jacobi hα 0).1
  · simpa using (rosenQ_jacobi hα 0).1
private theorem scaled_lt_pi {α u : ℝ} (hα : 0 < α) (hu : u < π / α) :
    α * u < π := by
  simpa [mul_comm] using (lt_div_iff₀ hα).mp hu

private theorem rosenP_pos {α u : ℝ} (hα : 0 < α) (hu : 0 < u)
    (hU : u < π / α) : 0 < rosenP α u :=
  div_pos (sin_pos_of_pos_of_lt_pi (mul_pos hα hu) (scaled_lt_pi hα hU)) hα
private theorem rosenQ_pos {α u : ℝ} (hα : 0 < α) (hu : 0 < u) : 0 < rosenQ α u :=
  div_pos (sinh_pos_iff.mpr (mul_pos hα hu)) hα

/-- The two transverse tidal traces cancel before the first caustic. -/
theorem rosen_ricci_flat {α u : ℝ} (hα : 0 < α) (hu : 0 < u) (hU : u < π / α) :
    deriv (deriv (rosenP α)) u / rosenP α u +
      deriv (deriv (rosenQ α)) u / rosenQ α u = 0 := by
  have hp : deriv (rosenP α) = fun w => cos (α * w) :=
    funext fun w => (rosenP_jacobi hα w).1.deriv
  have hq : deriv (rosenQ α) = fun w => cosh (α * w) :=
    funext fun w => (rosenQ_jacobi hα w).1.deriv
  rw [hp, hq, (rosenP_jacobi hα u).2.deriv, (rosenQ_jacobi hα u).2.deriv]
  field_simp [(rosenP_pos hα hu hU).ne', (rosenQ_pos hα hu).ne']
  ring

/-- Oscillatory entry of the exact Synge screen form. -/
def syngeQx (α u v : ℝ) : ℝ :=
  rosenP α u * rosenP α v * (α * (v - u)) / sin (α * (v - u))

/-- Hyperbolic entry of the exact Synge screen form. -/
def syngeQy (α u v : ℝ) : ℝ :=
  rosenQ α u * rosenQ α v * (α * (v - u)) / sinh (α * (v - u))

private theorem syngeQx_pos {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) : 0 < syngeQx α u v := by
  unfold syngeQx
  exact div_pos
    (mul_pos (mul_pos (rosenP_pos hα hu (huv.trans hV)) (rosenP_pos hα (hu.trans huv) hV))
      (mul_pos hα (sub_pos.mpr huv)))
    (sin_pos_of_pos_of_lt_pi (mul_pos hα (sub_pos.mpr huv))
      (scaled_lt_pi hα (by linarith)))
private theorem syngeQy_pos {α u v : ℝ} (hα : 0 < α) (hu : 0 < u) (huv : u < v) :
    0 < syngeQy α u v := by
  unfold syngeQy
  exact div_pos (mul_pos (mul_pos (rosenQ_pos hα hu) (rosenQ_pos hα (hu.trans huv)))
    (mul_pos hα (sub_pos.mpr huv))) (sinh_pos_iff.mpr (mul_pos hα (sub_pos.mpr huv)))

private theorem inv_rosenP_continuousOn {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (hV : v < π / α) : ContinuousOn (fun w => (rosenP α w)⁻¹ ^ 2) (Icc u v) := by
  have hc : Continuous (rosenP α) := by unfold rosenP; fun_prop
  exact (hc.continuousOn.inv₀ fun w hw => (rosenP_pos hα (hu.trans_le hw.1)
    (hw.2.trans_lt hV)).ne').pow 2

private theorem inv_rosenQ_continuousOn {α u v : ℝ} (hα : 0 < α) (hu : 0 < u) :
    ContinuousOn (fun w => (rosenQ α w)⁻¹ ^ 2) (Icc u v) := by
  have hc : Continuous (rosenQ α) := by unfold rosenQ; fun_prop
  exact (hc.continuousOn.inv₀ fun w hw => (rosenQ_pos hα (hu.trans_le hw.1)).ne').pow 2

private theorem rosenP_inv_integral {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    (∫ w in u..v, (rosenP α w)⁻¹ ^ 2) =
      α * sin (α * (v - u)) / (sin (α * u) * sin (α * v)) := by
  let F (w : ℝ) := -α * (cos (α * w) / sin (α * w))
  have hs (w : ℝ) (hw : w ∈ Icc u v) : 0 < sin (α * w) :=
    sin_pos_of_pos_of_lt_pi (mul_pos hα (hu.trans_le hw.1))
      (scaled_lt_pi hα (hw.2.trans_lt hV))
  have hFTC : (∫ w in u..v, (rosenP α w)⁻¹ ^ 2) = F v - F u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro w hw
      rw [uIcc_of_le huv.le] at hw
      have d := hasDerivAt_linear α w
      have dq := ((d.cos.div d.sin (hs w hw).ne').const_mul (-α))
      convert dq using 1
      unfold rosenP
      field_simp [(hs w hw).ne']
      nlinarith [sin_sq_add_cos_sq (α * w)]
    · exact (inv_rosenP_continuousOn hα hu hV).intervalIntegrable_of_Icc huv.le
  rw [hFTC]
  unfold F
  rw [mul_sub, sin_sub]
  field_simp [(hs u ⟨le_rfl, huv.le⟩).ne', (hs v ⟨huv.le, le_rfl⟩).ne']
  ring

private theorem rosenQ_inv_integral {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) :
    (∫ w in u..v, (rosenQ α w)⁻¹ ^ 2) =
      α * sinh (α * (v - u)) / (sinh (α * u) * sinh (α * v)) := by
  let F (w : ℝ) := -α * (cosh (α * w) / sinh (α * w))
  have hs (w : ℝ) (hw : w ∈ Icc u v) : 0 < sinh (α * w) :=
    sinh_pos_iff.mpr (mul_pos hα (hu.trans_le hw.1))
  have hFTC : (∫ w in u..v, (rosenQ α w)⁻¹ ^ 2) = F v - F u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro w hw
      rw [uIcc_of_le huv.le] at hw
      have d := hasDerivAt_linear α w
      have dq := ((d.cosh.div d.sinh (hs w hw).ne').const_mul (-α))
      convert dq using 1
      unfold rosenQ
      field_simp [(hs w hw).ne']
      nlinarith [cosh_sq_sub_sinh_sq (α * w)]
    · exact (inv_rosenQ_continuousOn hα hu).intervalIntegrable_of_Icc huv.le
  rw [hFTC]
  unfold F
  rw [mul_sub, sinh_sub]
  field_simp [(hs u ⟨le_rfl, huv.le⟩).ne', (hs v ⟨huv.le, le_rfl⟩).ne']
  ring

/-- Integrating the inverse oscillatory screen metric gives its exact Synge coefficient. -/
theorem syngeQx_eq_integral {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    syngeQx α u v = (v - u) / (∫ w in u..v, (rosenP α w)⁻¹ ^ 2) := by
  have hu' := sin_pos_of_pos_of_lt_pi (mul_pos hα hu) (scaled_lt_pi hα (huv.trans hV))
  have hv' := sin_pos_of_pos_of_lt_pi (mul_pos hα (hu.trans huv)) (scaled_lt_pi hα hV)
  have hd := sin_pos_of_pos_of_lt_pi (mul_pos hα (sub_pos.mpr huv))
    (scaled_lt_pi hα (show v - u < π / α by linarith))
  rw [rosenP_inv_integral hα hu huv hV]
  unfold syngeQx rosenP
  field_simp [hu'.ne', hv'.ne', hd.ne']

/-- Integrating the inverse hyperbolic screen metric gives its exact Synge coefficient. -/
theorem syngeQy_eq_integral {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) :
    syngeQy α u v = (v - u) / (∫ w in u..v, (rosenQ α w)⁻¹ ^ 2) := by
  have hu' := sinh_pos_iff.mpr (mul_pos hα hu)
  have hv' := sinh_pos_iff.mpr (mul_pos hα (hu.trans huv))
  have hd := sinh_pos_iff.mpr (mul_pos hα (sub_pos.mpr huv))
  rw [rosenQ_inv_integral hα hu huv]
  unfold syngeQy rosenQ
  field_simp [hu'.ne', hv'.ne', hd.ne']

private theorem sin_lt_sinh_of_pos {w : ℝ} (hw : 0 < w) : sin w < sinh w :=
  (sin_lt hw).trans (self_lt_sinh_iff.mpr hw)

/-- Both Synge coefficients are positive, and the hyperbolic direction is strictly larger. -/
theorem syngeQx_lt_syngeQy {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    0 < syngeQx α u v ∧ syngeQx α u v < syngeQy α u v := by
  refine ⟨syngeQx_pos hα hu huv hV, ?_⟩
  have hcompare (w : ℝ) (hw : w ∈ Icc u v) : (rosenQ α w)⁻¹ ^ 2 < (rosenP α w)⁻¹ ^ 2 := by
    have hw' := hu.trans_le hw.1
    have hp := rosenP_pos hα hw' (hw.2.trans_lt hV)
    have hlt : rosenP α w < rosenQ α w :=
      div_lt_div_of_pos_right (sin_lt_sinh_of_pos (mul_pos hα hw')) hα
    exact pow_lt_pow_left₀ (inv_lt_inv₀ (hp.trans hlt) hp |>.mpr hlt)
      (inv_nonneg.mpr (hp.trans hlt).le) (by decide)
  have hin := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt huv
    (inv_rosenQ_continuousOn hα hu) (inv_rosenP_continuousOn hα hu hV)
    (fun w hw => (hcompare w ⟨hw.1.le, hw.2⟩).le)
    ⟨u, ⟨le_rfl, huv.le⟩, hcompare u ⟨le_rfl, huv.le⟩⟩
  have hqpos : 0 < ∫ w in u..v, (rosenQ α w)⁻¹ ^ 2 :=
    intervalIntegral.integral_pos huv (inv_rosenQ_continuousOn hα hu)
      (fun w _ => sq_nonneg _) ⟨u, ⟨le_rfl, huv.le⟩, by
        exact pow_pos (inv_pos.mpr (rosenQ_pos hα hu)) _⟩
  rw [syngeQx_eq_integral hα hu huv hV, syngeQy_eq_integral hα hu huv]
  exact div_lt_div_of_pos_left (sub_pos.mpr huv) hqpos hin

/-- The area-normalized Hadamard angular coefficient. -/
def hadamardAnisotropy (α u v θ : ℝ) : ℝ :=
  sqrt (syngeQx α u v * syngeQy α u v) /
    (syngeQx α u v * (cos θ)^2 + syngeQy α u v * (sin θ)^2)

/-- The mixed difference of the angular coefficient over a radial rectangle. -/
def rectMismatch (α u₁ u₂ v₁ v₂ θ : ℝ) : ℝ :=
  hadamardAnisotropy α u₂ v₂ θ - hadamardAnisotropy α u₂ v₁ θ -
    hadamardAnisotropy α u₁ v₂ θ + hadamardAnisotropy α u₁ v₁ θ

/-- The axis value is the square root of the ratio of the two screen coefficients. -/
theorem hadamardAnisotropy_axis {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    hadamardAnisotropy α u v 0 = sqrt (syngeQy α u v / syngeQx α u v) := by
  have hx := syngeQx_pos hα hu huv hV
  have hy := syngeQy_pos hα hu huv
  simp only [hadamardAnisotropy, cos_zero, one_pow, mul_one, sin_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]
  apply (sq_eq_sq₀ (div_nonneg (sqrt_nonneg _) hx.le) (sqrt_nonneg _)).mp
  rw [div_pow, sq_sqrt (mul_nonneg hx.le hy.le), sq_sqrt (div_nonneg hy.le hx.le)]
  field_simp

private def tidalLog (w : ℝ) : ℝ := log (sinh w) - log (sin w)
private def tidalSlope (w : ℝ) : ℝ := cosh w / sinh w - cos w / sin w
private theorem tidalLog_deriv {w : ℝ} (hw : w ∈ Ioo 0 π) :
    HasDerivAt tidalLog (tidalSlope w) w :=
  ((hasDerivAt_sinh w).log (sinh_pos_iff.mpr hw.1).ne').sub
    ((hasDerivAt_sin w).log (sin_pos_of_pos_of_lt_pi hw.1 hw.2).ne')
private theorem tidalSlope_deriv {w : ℝ} (hw : w ∈ Ioo 0 π) :
    HasDerivAt tidalSlope ((sin w)⁻¹ ^ 2 - (sinh w)⁻¹ ^ 2) w := by
  have hs := sin_pos_of_pos_of_lt_pi hw.1 hw.2
  have hh := sinh_pos_iff.mpr hw.1
  unfold tidalSlope
  convert (((hasDerivAt_cosh w).div (hasDerivAt_sinh w) hh.ne').sub
    ((hasDerivAt_cos w).div (hasDerivAt_sin w) hs.ne')) using 1
  have hsin : -(sin w) * sin w - cos w * cos w = -1 := by
    nlinarith [sin_sq_add_cos_sq w]
  have hsinh : sinh w * sinh w - cosh w * cosh w = -1 := by
    nlinarith [cosh_sq_sub_sinh_sq w]
  rw [hsin, hsinh]
  field_simp [hs.ne', hh.ne']
  ring

private theorem tidalSlope_strictMonoOn : StrictMonoOn tidalSlope (Ioo 0 π) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 π)
  · exact fun w hw => (tidalSlope_deriv hw).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ioo] at hw
    rw [(tidalSlope_deriv hw).deriv, sub_pos]
    have hs := sin_pos_of_pos_of_lt_pi hw.1 hw.2
    have hh := hs.trans (sin_lt_sinh_of_pos hw.1)
    exact pow_lt_pow_left₀ ((inv_lt_inv₀ hh hs).mpr (sin_lt_sinh_of_pos hw.1))
      (inv_nonneg.mpr hh.le) (by decide)

private theorem tidalSlope_pos {w : ℝ} (hw : w ∈ Ioo 0 π) : 0 < tidalSlope w := by
  let N (x : ℝ) := cosh x * sin x - cos x * sinh x
  have hN : StrictMonoOn N (Ico 0 π) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 π) (by dsimp [N]; fun_prop)
    intro x hx
    rw [interior_Ico] at hx
    have hd := ((hasDerivAt_cosh x).mul (hasDerivAt_sin x)).sub
      ((hasDerivAt_cos x).mul (hasDerivAt_sinh x))
    change 0 < deriv (cosh * sin - cos * sinh) x
    rw [hd.deriv]
    have hprod := mul_pos (sinh_pos_iff.mpr hx.1) (sin_pos_of_pos_of_lt_pi hx.1 hx.2)
    nlinarith
  have hp : 0 < N w := by
    simpa [N] using hN ⟨le_rfl, pi_pos⟩ ⟨hw.1.le, hw.2⟩ hw.1
  have hs := sin_pos_of_pos_of_lt_pi hw.1 hw.2
  have hh := sinh_pos_iff.mpr hw.1
  unfold tidalSlope
  exact (sub_pos.mpr ((div_lt_div_iff₀ hs hh).mpr (by
    dsimp [N] at hp
    linarith)))

private def axisLog (α u v : ℝ) : ℝ :=
  (tidalLog (α * u) + tidalLog (α * v) - tidalLog (α * (v - u))) / 2
private theorem axisLog_deriv_left {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    HasDerivAt (fun w => axisLog α w v)
      (α * (tidalSlope (α * u) + tidalSlope (α * (v - u))) / 2) u := by
  have du := tidalLog_deriv ⟨mul_pos hα hu, scaled_lt_pi hα (huv.trans hV)⟩
  have dd := tidalLog_deriv
    ⟨mul_pos hα (sub_pos.mpr huv), scaled_lt_pi hα (show v-u < π / α by linarith)⟩
  have hd : HasDerivAt (fun w : ℝ => α * (v - w)) (-α) u := by
    simpa using ((hasDerivAt_id u).const_sub v).const_mul α
  unfold axisLog
  convert ((((du.comp u (hasDerivAt_linear α u)).add_const (tidalLog (α * v))).sub
    (dd.comp u hd)).div_const 2) using 1
  · rfl
  · ring
private theorem axisLog_deriv_right {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    HasDerivAt (axisLog α u)
      (α * (tidalSlope (α * v) - tidalSlope (α * (v - u))) / 2) v := by
  have dv := tidalLog_deriv ⟨mul_pos hα (hu.trans huv), scaled_lt_pi hα hV⟩
  have dd := tidalLog_deriv
    ⟨mul_pos hα (sub_pos.mpr huv), scaled_lt_pi hα (show v-u < π / α by linarith)⟩
  have hd : HasDerivAt (fun w : ℝ => α * (w - u)) α v := by
    simpa using ((hasDerivAt_id v).sub_const u).const_mul α
  unfold axisLog
  convert ((((dv.comp v (hasDerivAt_linear α v)).const_add (tidalLog (α * u))).sub
    (dd.comp v hd)).div_const 2) using 1
  · rfl
  · ring

private theorem axisLog_strictMonoOn_right {α u : ℝ} (hα : 0 < α) (hu : 0 < u) :
    StrictMonoOn (axisLog α u) (Ioo u (π / α)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo u (π / α))
  · exact fun v hv => (axisLog_deriv_right hα hu hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    rw [(axisLog_deriv_right hα hu hv.1 hv.2).deriv]
    refine div_pos (mul_pos hα (sub_pos.mpr (tidalSlope_strictMonoOn ?_ ?_ ?_))) (by norm_num)
    · exact ⟨mul_pos hα (sub_pos.mpr hv.1), scaled_lt_pi hα (by linarith [hv.2])⟩
    · exact ⟨mul_pos hα (hu.trans hv.1), scaled_lt_pi hα hv.2⟩
    · exact mul_lt_mul_of_pos_left (by linarith) hα

private theorem axisLog_exp {α u v : ℝ} (hα : 0 < α) (hu : 0 < u) (huv : u < v)
    (hV : v < π / α) : exp (axisLog α u v) = hadamardAnisotropy α u v 0 := by
  have up := mul_pos hα hu
  have vp := mul_pos hα (hu.trans huv)
  have dp := mul_pos hα (sub_pos.mpr huv)
  have su := sin_pos_of_pos_of_lt_pi up (scaled_lt_pi hα (huv.trans hV))
  have sv := sin_pos_of_pos_of_lt_pi vp (scaled_lt_pi hα hV)
  have sd := sin_pos_of_pos_of_lt_pi dp (scaled_lt_pi hα (by linarith))
  have qu := sinh_pos_iff.mpr up
  have qv := sinh_pos_iff.mpr vp
  have qd := sinh_pos_iff.mpr dp
  rw [hadamardAnisotropy_axis hα hu huv hV]
  apply (sq_eq_sq₀ (exp_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_sqrt (div_nonneg (syngeQy_pos hα hu huv).le (syngeQx_pos hα hu huv hV).le),
    ← exp_nat_mul]
  have ht (t : ℝ) (hs : 0 < sin t) (hq : 0 < sinh t) :
      exp (tidalLog t) = sinh t / sin t := by
    rw [tidalLog, exp_sub, exp_log hs, exp_log hq]
  unfold axisLog
  push_cast
  rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), exp_sub, exp_add, ht _ su qu,
    ht _ sv qv, ht _ sd qd]
  unfold syngeQx syngeQy rosenP rosenQ
  field_simp [su.ne', sv.ne', sd.ne', qu.ne', qv.ne', qd.ne', dp.ne']

/-- Every separated pre-caustic radial rectangle has a strictly positive axis mismatch. -/
theorem rectMismatch_axis_pos {α u₁ u₂ v₁ v₂ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁)
    (hu : u₁ < u₂) (huv : u₂ < v₁) (hv : v₁ < v₂) (hV : v₂ < π / α) :
    0 < rectMismatch α u₁ u₂ v₁ v₂ 0 := by
  have v₁c := hv.trans hV
  have hmono : StrictMonoOn
      (fun u => exp (axisLog α u v₂) - exp (axisLog α u v₁)) (Ioo 0 v₁) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 v₁)
    · intro u hu'
      exact (((axisLog_deriv_left hα hu'.1 (hu'.2.trans hv) hV).exp.sub
        (axisLog_deriv_left hα hu'.1 hu'.2 v₁c).exp).continuousAt).continuousWithinAt
    · intro u hu'
      rw [interior_Ioo] at hu'
      change 0 < deriv ((fun u => exp (axisLog α u v₂)) - fun u => exp (axisLog α u v₁)) u
      rw [((axisLog_deriv_left hα hu'.1 (hu'.2.trans hv) hV).exp.sub
        (axisLog_deriv_left hα hu'.1 hu'.2 v₁c).exp).deriv, sub_pos]
      have hlog := axisLog_strictMonoOn_right hα hu'.1
        ⟨hu'.2, v₁c⟩ ⟨hu'.2.trans hv, hV⟩ hv
      have hdu : α * u ∈ Ioo 0 π := ⟨mul_pos hα hu'.1, scaled_lt_pi hα (hu'.2.trans v₁c)⟩
      have hd₁ : α * (v₁ - u) ∈ Ioo 0 π :=
        ⟨mul_pos hα (sub_pos.mpr hu'.2), scaled_lt_pi hα (by linarith [hu'.1])⟩
      have hd₂ : α * (v₂ - u) ∈ Ioo 0 π :=
        ⟨mul_pos hα (sub_pos.mpr (hu'.2.trans hv)), scaled_lt_pi hα (by linarith [hu'.1])⟩
      have hslope := tidalSlope_strictMonoOn hd₁ hd₂ (mul_lt_mul_of_pos_left (by linarith) hα)
      have hpos := add_pos (tidalSlope_pos hdu) (tidalSlope_pos hd₁)
      have hL := mul_lt_mul_of_pos_right (exp_lt_exp.mpr hlog)
        (div_pos (mul_pos hα hpos) (by norm_num : (0 : ℝ) < 2))
      have hR := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_left hslope.le (tidalSlope (α * u))) hα.le)
          (by norm_num : (0 : ℝ) ≤ 2)) (exp_nonneg (axisLog α u v₂))
      exact hL.trans_le (by simpa only [add_comm] using hR)
  have hh := hmono ⟨hu₁, hu.trans huv⟩ ⟨hu₁.trans hu, huv⟩ hu
  simp only [axisLog_exp hα (hu₁.trans hu) (huv.trans hv) hV,
    axisLog_exp hα (hu₁.trans hu) huv v₁c,
    axisLog_exp hα hu₁ (hu.trans (huv.trans hv)) hV,
    axisLog_exp hα hu₁ (hu.trans huv) v₁c] at hh
  unfold rectMismatch
  linarith

/-- An explicit nonzero rectangle lies below any prescribed pre-caustic affine scale. -/
theorem exists_rectMismatch_ne_zero {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hcut : δ ≤ π / α) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, 0 < u₁ ∧ u₁ < u₂ ∧ u₂ < v₁ ∧ v₁ < v₂ ∧ v₂ < δ ∧
      rectMismatch α u₁ u₂ v₁ v₂ 0 ≠ 0 := by
  have hV : 4 * δ / 5 < δ := by linarith
  refine ⟨δ / 5, 2 * δ / 5, 3 * δ / 5, 4 * δ / 5,
    by linarith, by linarith, by linarith, by linarith, hV, ?_⟩
  exact (rectMismatch_axis_pos hα (by linarith) (by linarith) (by linarith) (by linarith)
    (hV.trans_le hcut)).ne'

/-- Parameter of the Poisson kernel at twice the screen angle. -/
def hadamardPoissonParameter (α u v : ℝ) : ℝ :=
  (sqrt (syngeQy α u v) - sqrt (syngeQx α u v)) /
    (sqrt (syngeQy α u v) + sqrt (syngeQx α u v))

/-- Strict Weyl anisotropy puts the Poisson parameter in the open unit interval. -/
theorem hadamardPoissonParameter_mem_Ioo {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    hadamardPoissonParameter α u v ∈ Ioo 0 1 :=
  let h := syngeQx_lt_syngeQy hα hu huv hV
  Omega.ScreenAnisotropy.parameter_mem_Ioo h.1 h.2

/-- The area-normalized coefficient is the Poisson kernel at twice the screen angle. -/
theorem hadamardAnisotropy_eq_poisson {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) (θ : ℝ) :
    hadamardAnisotropy α u v θ =
      Omega.ScreenAnisotropy.poisson (hadamardPoissonParameter α u v) (2 * θ) :=
  Omega.ScreenAnisotropy.factor_eq_poisson (syngeQx_pos hα hu huv hV) (syngeQy_pos hα hu huv) θ

/-- Area normalization gives angular mean one for each radial pair. -/
theorem hadamardAnisotropy_average {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) :
    (1 / (2 * π)) * (∫ θ in (0 : ℝ)..(2 * π), hadamardAnisotropy α u v θ) = 1 :=
  Omega.ScreenAnisotropy.factor_average (syngeQx_pos hα hu huv hV) (syngeQy_pos hα hu huv)

/-- The exact angular inner product is determined by the product of the two Poisson parameters. -/
theorem hadamardAnisotropy_inner {α u₁ v₁ u₂ v₂ : ℝ} (hα : 0 < α)
    (hu₁ : 0 < u₁) (huv₁ : u₁ < v₁) (hv₁ : v₁ < π / α)
    (hu₂ : 0 < u₂) (huv₂ : u₂ < v₂) (hv₂ : v₂ < π / α) :
    (∫ θ in (0 : ℝ)..(2 * π), hadamardAnisotropy α u₁ v₁ θ * hadamardAnisotropy α u₂ v₂ θ) =
      2 * π * (1 + hadamardPoissonParameter α u₁ v₁ * hadamardPoissonParameter α u₂ v₂) /
        (1 - hadamardPoissonParameter α u₁ v₁ * hadamardPoissonParameter α u₂ v₂) :=
  Omega.ScreenAnisotropy.factor_inner (syngeQx_pos hα hu₁ huv₁ hv₁) (syngeQy_pos hα hu₁ huv₁)
    (syngeQx_pos hα hu₂ huv₂ hv₂) (syngeQy_pos hα hu₂ huv₂)

private theorem continuous_hadamardAnisotropy {α u v : ℝ} (hα : 0 < α) (hu : 0 < u)
    (huv : u < v) (hV : v < π / α) : Continuous (hadamardAnisotropy α u v) :=
  Omega.ScreenAnisotropy.continuous_factor (syngeQx_pos hα hu huv hV) (syngeQy_pos hα hu huv)

private theorem continuous_rectMismatch {α u₁ u₂ v₁ v₂ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁)
    (hu : u₁ < u₂) (huv : u₂ < v₁) (hv : v₁ < v₂) (hV : v₂ < π / α) :
    Continuous (rectMismatch α u₁ u₂ v₁ v₂) := by
  unfold rectMismatch
  exact (((continuous_hadamardAnisotropy hα (hu₁.trans hu) (huv.trans hv) hV).sub
    (continuous_hadamardAnisotropy hα (hu₁.trans hu) huv (hv.trans hV))).sub
      (continuous_hadamardAnisotropy hα hu₁ (hu.trans (huv.trans hv)) hV)).add
        (continuous_hadamardAnisotropy hα hu₁ (hu.trans huv) (hv.trans hV))

/-- Each separated pre-caustic radial rectangle has positive squared angular mismatch. -/
theorem rectMismatch_integral_sq_pos {α u₁ u₂ v₁ v₂ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁)
    (hu : u₁ < u₂) (huv : u₂ < v₁) (hv : v₁ < v₂) (hV : v₂ < π / α) :
    0 < ∫ θ in (0 : ℝ)..(2 * π), (rectMismatch α u₁ u₂ v₁ v₂ θ) ^ 2 :=
  Omega.ScreenAnisotropy.integral_sq_pos_of_ne_zero
    (continuous_rectMismatch hα hu₁ hu huv hv hV) (rectMismatch_axis_pos hα hu₁ hu huv hv hV).ne'

/-- Positive equal screen coefficients give unit angular factor and zero mixed difference. -/
theorem screen_zero_shear (Qx Qy : ℝ → ℝ → ℝ)
    (hpos : ∀ u v, 0 < Qx u v) (heq : ∀ u v, Qx u v = Qy u v) :
    (∀ u v θ, Omega.ScreenAnisotropy.factor (Qx u v) (Qy u v) θ = 1) ∧
    (∀ u₁ u₂ v₁ v₂ θ,
      Omega.ScreenAnisotropy.factor (Qx u₂ v₂) (Qy u₂ v₂) θ -
        Omega.ScreenAnisotropy.factor (Qx u₂ v₁) (Qy u₂ v₁) θ -
        Omega.ScreenAnisotropy.factor (Qx u₁ v₂) (Qy u₁ v₂) θ +
        Omega.ScreenAnisotropy.factor (Qx u₁ v₁) (Qy u₁ v₁) θ = 0) := by
  have h u v θ : Omega.ScreenAnisotropy.factor (Qx u v) (Qy u v) θ = 1 := by
    rw [← heq u v]
    exact Omega.ScreenAnisotropy.factor_self (hpos u v) θ
  exact ⟨h, fun u₁ u₂ v₁ v₂ θ => by simp only [h]; norm_num⟩

/-- A sector of inverse-square growth in the real two-dimensional screen excludes L². -/
theorem shear_kernel_not_L2_on_ball {K : ℂ × ℂ → ℂ} {z : ℂ} {R ρ c a b : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hc : 0 < c) (ha : -π ≤ a) (hab : a < b) (hb : b ≤ π)
    (hK : ∀ᵐ p ∂((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))),
      0 < ‖p.1 - p.2‖ → ‖p.1 - p.2‖ < ρ →
        Complex.arg (p.1 - p.2) ∈ Ioo a b → c / ‖p.1 - p.2‖ ^ 2 ≤ ‖K p‖) :
    ¬ MemLp K 2 ((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))) :=
  Omega.planarWedge_not_memLp hR hρ hc ha hab hb hK

/-- The exact square integral per unit screen area for the rectangle coefficient. -/
theorem rectMismatch_annulus_squared (α u₁ u₂ v₁ v₂ : ℝ) {ε ρ : ℝ}
    (hε : 0 < ε) (hερ : ε < ρ) :
    (∫ r in ε..ρ, (∫ θ in (0 : ℝ)..(2 * π), (rectMismatch α u₁ u₂ v₁ v₂ θ / r ^ 2) ^ 2) * r) =
      (1 / 2 : ℝ) * (∫ θ in (0 : ℝ)..(2 * π), (rectMismatch α u₁ u₂ v₁ v₂ θ) ^ 2) *
        ((ε ^ 2)⁻¹ - (ρ ^ 2)⁻¹) :=
  Omega.polar_annulus_squared (rectMismatch α u₁ u₂ v₁ v₂) hε hερ

/-- The annular square integral diverges for every separated pre-caustic radial rectangle. -/
theorem rectMismatch_annulus_diverges {α u₁ u₂ v₁ v₂ ρ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁)
    (hu : u₁ < u₂) (huv : u₂ < v₁) (hv : v₁ < v₂) (hV : v₂ < π / α) (hρ : 0 < ρ) :
    Filter.Tendsto (fun ε : ℝ => ∫ r in ε..ρ,
      (∫ θ in (0 : ℝ)..(2 * π), (rectMismatch α u₁ u₂ v₁ v₂ θ / r ^ 2) ^ 2) * r)
        (𝓝[>] 0) Filter.atTop :=
  Omega.tendsto_polar_annulus_squared (rectMismatch α u₁ u₂ v₁ v₂) hρ
    (rectMismatch_integral_sq_pos hα hu₁ hu huv hv hV)

/-- The characteristic pairing gives the angular mismatch divided by π² and squared separation. -/
def planeWavePointConeShearKernel (α u₁ u₂ v₁ v₂ : ℝ) : ℂ × ℂ → ℂ :=
  Omega.angularKernel fun θ => rectMismatch α u₁ u₂ v₁ v₂ θ / π ^ 2

/-- Every separated radial rectangle before the first caustic obstructs square integrability
of the exact plane-wave point-cone shear term on every nonempty screen ball. -/
theorem planeWave_pointCone_shear_not_L2 {α u₁ u₂ v₁ v₂ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁)
    (hu : u₁ < u₂) (huv : u₂ < v₁) (hv : v₁ < v₂) (hV : v₂ < π / α)
    (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ¬ MemLp (planeWavePointConeShearKernel α u₁ u₂ v₁ v₂) 2
      ((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))) :=
  Omega.angularKernel_not_memLp ((continuous_rectMismatch hα hu₁ hu huv hv hV).div_const _)
    (div_ne_zero (rectMismatch_axis_pos hα hu₁ hu huv hv hV).ne' (pow_ne_zero _ pi_ne_zero))
    z hR

/-- Every Hilbert–Schmidt operator on complex L² has an L² integral kernel. -/
theorem hilbertSchmidt_has_integral_kernel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) :
    ∃ (J : X × X → ℂ) (hJ : MemLp J 2 (μ.prod μ)), integralKernelOp μ J hJ = T := by
  obtain ⟨_, b, hb⟩ := hT
  obtain ⟨k, hk⟩ := Omega.exists_l2_kernel_of_summable_basis μ b (fun i => T (b i)) hb
  refine ⟨k, Lp.memLp k, ?_⟩
  ext1 g
  apply ext_inner_left ℂ
  intro f
  calc
    ⟪f, integralKernelOp μ _ (Lp.memLp k) g⟫_ℂ =
        ⟪Omega.rankKernel μ f g, k⟫_ℂ := by
      rw [integralKernelOp_inner, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Omega.rankKernel_ae μ f g] with p hp
      rw [RCLike.inner_apply', hp]
      change star (f p.1) * k p * g p.2 = star (f p.1 * star (g p.2)) * k p
      rw [star_mul, star_star]
      ring
    _ = ⟪f, T g⟫_ℂ := by
      rw [hk]
      have hs := ((b.hasSum_repr g).mapL T).mapL (innerSL ℂ f)
      simpa only [map_smul, innerSL_apply_apply, inner_smul_right, smul_eq_mul,
        b.repr_apply_apply, mul_comm] using hs.tsum_eq

/-- The operator represents the locally integrable off-diagonal kernel on separated rectangles. -/
def RepresentsKernelOffDiagonal (μ : Measure ℂ) [IsFiniteMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (K : ℂ × ℂ → ℂ) : Prop :=
  ∀ s t : Set ℂ, ∀ (hs : MeasurableSet s) (ht : MeasurableSet t), Omega.PositivelySeparated s t →
    IntegrableOn K (s ×ˢ t) (μ.prod μ) ∧
      ⟪indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ),
        T (indicatorConstLp 2 ht (measure_ne_top μ t) (1 : ℂ))⟫_ℂ =
        ∫ p in s ×ˢ t, K p ∂(μ.prod μ)

/-- A sector singularity excludes Hilbert–Schmidt representation on separated tests. -/
theorem shear_obstruction_no_hilbertSchmidt_kernel {K : ℂ × ℂ → ℂ} {z : ℂ} {R ρ c a b : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hc : 0 < c) (ha : -π ≤ a) (hab : a < b) (hb : b ≤ π)
    (hK : ∀ᵐ p ∂((volume.restrict (Metric.ball z R)).prod (volume.restrict (Metric.ball z R))),
      0 < ‖p.1 - p.2‖ → ‖p.1 - p.2‖ < ρ →
        Complex.arg (p.1 - p.2) ∈ Ioo a b → c / ‖p.1 - p.2‖ ^ 2 ≤ ‖K p‖) :
    let μ : Measure ℂ := volume.restrict (Metric.ball z R)
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    ¬ ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
        HilbertSchmidt.IsHilbertSchmidt T ∧ RepresentsKernelOffDiagonal μ T K := by
  dsimp only
  let μ : Measure ℂ := volume.restrict (Metric.ball z R)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  rintro ⟨T, hT, hrep⟩
  obtain ⟨J, hJ, hOp⟩ := hilbertSchmidt_has_integral_kernel μ T hT
  have hEq := Omega.ae_eq_offDiagonal_of_rectangle_integrals
    (MemLp.integrable (by norm_num) hJ) (fun s t hs ht hst => (hrep s t hs ht hst).1) (by
      intro s t hs ht hst
      rw [← (hrep s t hs ht hst).2, ← hOp, integralKernelOp_inner, ← integral_indicator (hs.prod ht)]
      apply integral_congr_ae
      filter_upwards [(quasiMeasurePreserving_fst (ν := μ)).ae
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℂ))),
        (quasiMeasurePreserving_snd (μ := μ)).ae
          (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := measure_ne_top μ t) (c := (1 : ℂ)))] with p hp hq
      rw [hp, hq]
      by_cases hps : p.1 ∈ s <;> by_cases hpt : p.2 ∈ t <;> simp [hps, hpt])
  apply shear_kernel_not_L2_on_ball hR hρ hc ha hab hb (K := J) _ hJ
  filter_upwards [hK, hEq] with p hbound heq hp hsmall harg
  have hne : p.1 ≠ p.2 := fun h => by simp [h] at hp
  rw [heq hne]
  exact hbound hp hsmall harg

end NullConeGravity
