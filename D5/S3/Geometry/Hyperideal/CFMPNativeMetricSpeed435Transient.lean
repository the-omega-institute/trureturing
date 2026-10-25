import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeCoordinates435Transient
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalNativeCoordinates435Transient

namespace CFMPNativeMetricSpeed435Transient

def arsinhRatio : ℝ → ℝ := Function.update (fun x => Real.arsinh x/x) 0 1

theorem arsinhRatio_continuousAt : ContinuousAt arsinhRatio 0 := by
  have h : HasDerivAt Real.arsinh 1 0 := by simpa using Real.hasDerivAt_arsinh 0
  simpa [arsinhRatio] using h.continuousAt_div

theorem arsinhRatio_mul (x : ℝ) : arsinhRatio x*x = Real.arsinh x := by
  by_cases hx : x = 0
  · simp [hx,arsinhRatio]
  · simp [arsinhRatio,Function.update_of_ne hx,hx]

-- This norm is the existing L2 norm on Complex × Real.
-- Zero velocity is included; no punctured image assumption is used.
theorem native_metric_speed (γ : ℝ → UpperHalfSpace ℂ) (v : Ambient ℂ)
    (hγ : HasDerivAt (fun t => (γ t).val) v 0) :
    Tendsto (fun t => dist (HyperbolicSpace.mk (γ 0)) (HyperbolicSpace.mk (γ t))/|t|)
      (𝓝[≠] 0) (𝓝 (‖v‖/height (γ 0))) := by
  let H : ℝ → ℝ := fun t => height (γ t)
  let D : ℝ → ℝ := fun t => ‖(γ t).val-(γ 0).val‖
  let den : ℝ → ℝ := fun t => Real.sqrt (H 0*H t)
  let a : ℝ → ℝ := fun t => D t/(2*den t)
  have hH : ContinuousAt H 0 :=
    ((WithLp.sndL 2 ℝ ℂ ℝ).continuous.continuousAt).comp hγ.continuousAt
  have hD : ContinuousAt D 0 := (hγ.continuousAt.sub continuousAt_const).norm
  have hden : ContinuousAt den 0 :=
    Real.continuous_sqrt.continuousAt.comp (continuousAt_const.mul hH)
  have hdenpos (t : ℝ) : 0 < den t :=
    Real.sqrt_pos.mpr (mul_pos (γ 0).property (γ t).property)
  have hden0 : den 0 = H 0 := Real.sqrt_mul_self (γ 0).property.le
  have ha : ContinuousAt a 0 := hD.div (continuousAt_const.mul hden)
    (mul_ne_zero (by norm_num) (hdenpos 0).ne')
  have ha0 : a 0 = 0 := by simp [a,D]
  have hratio : Tendsto (fun t => arsinhRatio (a t)) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun t : ℝ => arsinhRatio (a t)) (𝓝[≠] 0)
        (𝓝 (arsinhRatio 0)) := arsinhRatio_continuousAt.tendsto.comp
      ((show Tendsto a (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) by simpa [ha0] using ha.tendsto).mono_left
        nhdsWithin_le_nhds)
    simpa [arsinhRatio] using h
  have hspeed : Tendsto (fun t => D t/|t|) (𝓝[≠] 0) (𝓝 ‖v‖) := by
    convert hγ.tendsto_slope_zero.norm using 1
    funext t
    simp [D,norm_smul,Real.norm_eq_abs,abs_inv,div_eq_mul_inv,mul_comm]
  have hdlim : Tendsto den (𝓝[≠] 0) (𝓝 (H 0)) := by
    simpa only [hden0] using hden.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hratio.mul hspeed).div hdlim (γ 0).property.ne'
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  change arsinhRatio (a t)*(D t/|t|)/den t =
    2*Real.arsinh (dist (γ 0).val (γ t).val/(2*Real.sqrt (H 0*H t)))/|t|
  have he : dist (γ 0).val (γ t).val = D t := by
    rw [dist_comm,dist_eq_norm]
  rw [he,← arsinhRatio_mul (a t)]
  change _ = 2*(arsinhRatio (a t)*(D t/(2*den t)))/|t|
  field_simp [(hdenpos t).ne',abs_ne_zero.mpr ht']
  <;> ring

-- Packing has a different source norm; the squared-norm identity supplies
-- the exact Euclidean coordinate meaning rather than identifying sup with L2.
def packLinear : V →ₗ[ℝ] Ambient ℂ where
  toFun v := WithLp.toLp 2 (Complex.mk (v 0) (v 1),v 2)
  map_add' v w := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply Complex.ext <;> rfl
    · rfl
  map_smul' c v := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply Complex.ext <;> simp [smul_eq_mul]
    · simp [smul_eq_mul]

theorem packLinear_norm_sq (v : V) :
    ‖packLinear v‖^2 = dotProduct v v := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Complex.mk (v 0) (v 1))‖^2+‖v 2‖^2 = _
  rw [Complex.sq_norm]
  simp [Complex.normSq_mk,Real.norm_eq_abs,sq_abs,
    dotProduct,Fin.sum_univ_three,pow_two]

theorem native_coordinate_speed (γ : ℝ → UpperHalfSpace ℂ) (w : V)
    (hγ : HasDerivAt (fun t => (γ t).val) (packLinear w) 0) :
    Tendsto (fun t => (dist (HyperbolicSpace.mk (γ 0)) (HyperbolicSpace.mk (γ t))/|t|)^2)
      (𝓝[≠] 0) (𝓝 (dotProduct w w/(height (γ 0))^2)) := by
  simpa [div_pow,packLinear_norm_sq] using (native_metric_speed γ (packLinear w) hγ).pow 2

end CFMPNativeMetricSpeed435Transient
