/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondDeSitterKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: De Sitter characteristic flux, conformal kernel, Frobenius coefficients and antipodal obstruction. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import Mathlib.Analysis.Analytic.Binomial
import D5.S3.Analysis.EndpointDerivative
import D5.S3.Analysis.LogarithmicEndpoint
import D5.S3.Analysis.LogisticCoordinate
import D5.S3.Analysis.MixedDerivativePairing
import D5.S3.Analysis.SphericalAngularMoment
import D5.S3.Analysis.TranslatedFourierPacket
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.PowerSeries.Derivative

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology FourierTransform RealInnerProductSpace

namespace NullConeGravity

/-- Conformal coordinate on a null generator in the expanding chart. -/
def dsMobius (T u : ℝ) : ℝ := u / (T - u)

/-- Conformal factor on the generator. -/
def dsOmega (H T u : ℝ) : ℝ := 1 / (H * (T - u))

/-- The affine parameter, normalized to vanish at the tip. -/
def dsAffine (H T u : ℝ) : ℝ := dsMobius T u / (H ^ 2 * T)

theorem ds_mobius_hasDerivAt {T u : ℝ} (hu : u < T) :
    HasDerivAt (dsMobius T) (T / (T - u) ^ 2) u := by
  have h := (hasDerivAt_id u).div ((hasDerivAt_const u T).sub (hasDerivAt_id u))
    (sub_ne_zero.mpr (ne_of_gt hu))
  convert h using 1
  · rfl
  · change T / (T - u) ^ 2 = (1 * (T - u) - u * (0 - 1)) / (T - u) ^ 2
    ring
theorem ds_affine_hasDerivAt {H T u : ℝ} (hH : 0 < H) (hT : 0 < T) (hu : u < T) :
    HasDerivAt (dsAffine H T) (dsOmega H T u ^ 2) u := by
  convert (ds_mobius_hasDerivAt hu).div_const (H ^ 2 * T) using 1
  · rfl
  · change (1 / (H * (T - u))) ^ 2 = T / (T - u) ^ 2 / (H ^ 2 * T)
    field_simp [(sub_pos.mpr hu).ne']

private theorem ds_radius_eq (H T u : ℝ) :
    u * dsOmega H T u = dsMobius T u / H := by
  simp [dsOmega, dsMobius, div_eq_mul_inv, mul_inv_rev, mul_left_comm, mul_comm]

theorem ds_flux_wronskian_eq {H T κ u : ℝ} {φ₁ φ₂ : ℝ → ℝ}
    (hH : 0 < H) (hu : 0 < u) (huT : u < T)
    (h₁ : DifferentiableAt ℝ φ₁ u) (h₂ : DifferentiableAt ℝ φ₂ u) :
    let ρ := fun t => t * dsOmega H T t
    let affineDeriv := deriv (dsAffine H T) u
    let Φ₁ := fun t => ρ t ^ κ * φ₁ t
    let Φ₂ := fun t => ρ t ^ κ * φ₂ t
    affineDeriv * ρ u ^ (2 * κ) * (φ₁ u * (deriv φ₂ u / affineDeriv) - φ₂ u * (deriv φ₁ u / affineDeriv)) =
      Φ₁ u * deriv Φ₂ u - Φ₂ u * deriv Φ₁ u := by
  dsimp only
  let ρ := fun t => t * dsOmega H T t
  have hρ : 0 < ρ u := by
    dsimp [ρ, dsOmega]
    positivity
  have hr : DifferentiableAt ℝ ρ u := by
    have he : ρ = fun t => dsMobius T t / H := funext (ds_radius_eq H T)
    rw [he]
    exact ((ds_mobius_hasDerivAt huT).div_const H).differentiableAt
  have hp : DifferentiableAt ℝ (fun t => ρ t ^ κ) u :=
    (hr.hasDerivAt.rpow_const (Or.inl hρ.ne')).differentiableAt
  have hl : deriv (dsAffine H T) u ≠ 0 := by
    rw [(ds_affine_hasDerivAt hH (hu.trans huT) huT).deriv]
    exact pow_ne_zero _ (one_div_ne_zero (mul_ne_zero hH.ne' (sub_pos.mpr huT).ne'))
  change _ = ρ u ^ κ * φ₁ u * deriv (fun t => ρ t ^ κ * φ₂ t) u -
    ρ u ^ κ * φ₂ u * deriv (fun t => ρ t ^ κ * φ₁ t) u
  erw [(hp.hasDerivAt.mul h₂.hasDerivAt).deriv, (hp.hasDerivAt.mul h₁.hasDerivAt).deriv]
  change deriv (dsAffine H T) u * ρ u ^ (2 * κ) * _ = _
  rw [two_mul, Real.rpow_add hρ]
  field_simp
  ring

private theorem ds_mobius_sub {T u v : ℝ} (hu : u < T) (hv : v < T) :
    dsMobius T u - dsMobius T v = T * (u - v) / ((T - u) * (T - v)) := by
  have hu' := (sub_pos.mpr hu).ne'
  have hv' := (sub_pos.mpr hv).ne'
  unfold dsMobius
  field_simp
  ring

theorem ds_mobius_log_eq {T u v : ℝ} (hT : 0 < T) (hu : u < T) (hv : v < T)
    (huv : u ≠ v) :
    Real.log (dsMobius T u - dsMobius T v) =
      Real.log T + Real.log (u - v) - Real.log (T - u) - Real.log (T - v) := by
  have hn := sub_ne_zero.mpr huv
  have hu' := (sub_pos.mpr hu).ne'
  have hv' := (sub_pos.mpr hv).ne'
  rw [ds_mobius_sub hu hv, Real.log_div (mul_ne_zero hT.ne' hn) (mul_ne_zero hu' hv'),
    Real.log_mul hT.ne' hn, Real.log_mul hu' hv']
  ring
theorem ds_mobius_log_mixed_deriv {T u v : ℝ} (hT : 0 < T) (hu : u < T) (hv : v < T)
    (huv : u ≠ v) :
    deriv (fun x => deriv (fun y => Real.log (dsMobius T x - dsMobius T y)) v) u =
      deriv (fun x => deriv (fun y => Real.log (x - y)) v) u := by
  have hplain : ∀ {x : ℝ}, x ≠ v →
      HasDerivAt (fun y => Real.log (x - y)) (-(x - v)⁻¹) v := by
    intro x hx
    simpa [div_eq_mul_inv] using ((hasDerivAt_const v x).sub (hasDerivAt_id v)).log (sub_ne_zero.mpr hx)
  have haux : ∀ {x : ℝ}, x < T → x ≠ v →
      deriv (fun y => Real.log (dsMobius T x - dsMobius T y)) v =
        deriv (fun y => Real.log (x - y)) v + (T - v)⁻¹ := by
    intro x hx hxv
    have he : (fun y => Real.log (dsMobius T x - dsMobius T y)) =ᶠ[𝓝 v]
        (fun y => (Real.log T - Real.log (T - x)) + Real.log (x - y) - Real.log (T - y)) := by
      filter_upwards [gt_mem_nhds hv, isOpen_ne.mem_nhds hxv.symm] with y hy hyx
      rw [ds_mobius_log_eq hT hx hy hyx.symm]
      ring
    have hh := (((hasDerivAt_const v (Real.log T - Real.log (T - x))).add
      (hplain hxv)).sub (((hasDerivAt_const v T).sub (hasDerivAt_id v)).log
        (sub_pos.mpr hv).ne')).congr_of_eventuallyEq he
    rw [hh.deriv, (hplain hxv).deriv]
    simp [div_eq_mul_inv]
  have he : (fun x => deriv (fun y => Real.log (dsMobius T x - dsMobius T y)) v) =ᶠ[𝓝 u]
      (fun x => deriv (fun y => Real.log (x - y)) v + (T - v)⁻¹) := by
    filter_upwards [gt_mem_nhds hu, isOpen_ne.mem_nhds huv] with x hx hxv
    exact haux hx hxv
  rw [he.deriv_eq, deriv_add_const]

/-- The complex boundary logarithm in affine coordinates differs almost everywhere from
the one in conformal coordinates by a sum of separate radial terms. -/
theorem ds_affine_boundary_log_ae {H T : ℝ} (hH : 0 < H) (hT : 0 < T) :
    let μ := (volume : Measure ℝ).restrict (Iio T)
    ∀ᵐ z ∂μ.prod μ, Complex.log (Complex.I * ((dsAffine H T z.1 - dsAffine H T z.2 : ℝ) : ℂ)) =
      Complex.log (Complex.I * ((z.1 - z.2 : ℝ) : ℂ)) -
      (Real.log (H ^ 2) + Real.log (T - z.1) + Real.log (T - z.2) : ℝ) := by
  let μ := (volume : Measure ℝ).restrict (Iio T)
  have hdom : ∀ᵐ u ∂μ, u < T := ae_restrict_mem measurableSet_Iio
  have hd : ∀ᵐ z ∂μ.prod μ, z.1 < T ∧ z.2 < T ∧ z.1 ≠ z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by dsimp; measurability)]
    filter_upwards [hdom] with u hu
    filter_upwards [hdom, μ.ae_ne u] with v hv huv using ⟨hu, hv, huv.symm⟩
  filter_upwards [hd] with z hz
  obtain ⟨hu, hv, huv⟩ := hz
  have ha : 0 < H ^ 2 := pow_pos hH _
  have hb := sub_pos.mpr hu
  have hc := sub_pos.mpr hv
  have he : dsAffine H T z.1 - dsAffine H T z.2 =
      (1 / (H ^ 2 * (T - z.1) * (T - z.2))) * (z.1 - z.2) := by
    rw [dsAffine, dsAffine, ← sub_div, ds_mobius_sub hu hv]
    field_simp
  rw [he, Complex.ofReal_mul, mul_left_comm Complex.I, Complex.log_ofReal_mul (by positivity)
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr huv))),
    Real.log_div one_ne_zero (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hc.ne'),
    Real.log_mul (mul_ne_zero ha.ne' hb.ne') hc.ne', Real.log_mul ha.ne' hb.ne']
  push_cast
  simp
  ring

/-- The difference of the boundary logarithms has zero weak mixed derivative on product tests. -/
theorem ds_affine_boundary_log_mixed_weak {H T a b : ℝ} {F G : ℝ → ℝ}
    (hH : 0 < H) (hT : 0 < T) (hab : a ≤ b) (hbT : b < T)
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFa : F a = 0) (hFb : F b = 0) (hGa : G a = 0) (hGb : G b = 0) :
    let μ := (volume : Measure ℝ).restrict (Ioc a b)
    ∫ z : ℝ × ℝ, (Complex.log (Complex.I * ((dsAffine H T z.1 - dsAffine H T z.2 : ℝ) : ℂ)) -
      Complex.log (Complex.I * ((z.1 - z.2 : ℝ) : ℂ))) *
        ((deriv F z.1 : ℝ) : ℂ) * ((deriv G z.2 : ℝ) : ℂ) ∂μ.prod μ = 0 := by
  have hc : ContinuousOn (fun x => Real.log (T - x)) (Icc a b) := fun x hx =>
    ((Real.continuousAt_log (sub_pos.mpr (hx.2.trans_lt hbT)).ne').comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  apply Omega.integral_mul_deriv_product_eq_zero_of_ae_separate (s := Iio T)
    (A := fun x => -(↑(Real.log (H ^ 2) + Real.log (T - x)) : ℂ))
    (B := fun x => -(↑(Real.log (T - x)) : ℂ)) hab (fun x hx => hx.2.trans_lt hbT)
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.add hc)).neg
    (Complex.continuous_ofReal.comp_continuousOn hc).neg hF hG hFa hFb hGa hGb
  filter_upwards [ds_affine_boundary_log_ae hH hT] with z hz
  rw [hz]
  push_cast
  ring

/-- The squared chord variable divided by four, in the conventions of the kernel. -/
def dsChord (T y u v : ℝ) : ℝ := (y / 4) * dsMobius T u * dsMobius T v

private theorem ds_weight_cancel {H T κ y u v : ℝ}
    (hH : 0 < H) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) (huT : u < T) (hvT : v < T) :
    (u * dsOmega H T u) ^ κ * (v * dsOmega H T v) ^ κ * dsChord T y u v ^ (-κ) =
      H ^ (-2 * κ) * (4 / y) ^ κ := by
  have hfu : 0 < dsMobius T u := div_pos hu (sub_pos.mpr huT)
  have hfv : 0 < dsMobius T v := div_pos hv (sub_pos.mpr hvT)
  have hq : 0 < y / 4 := by positivity
  rw [ds_radius_eq, ds_radius_eq, dsChord, Real.mul_rpow (mul_nonneg hq.le hfu.le) hfv.le,
    Real.mul_rpow hq.le hfu.le, Real.div_rpow hfu.le hH.le, Real.div_rpow hfv.le hH.le,
    Real.rpow_neg hfu.le, Real.rpow_neg hfv.le, Real.rpow_neg hq.le,
    show -2 * κ = -(κ + κ) by ring, Real.rpow_neg hH.le, Real.rpow_add hH,
    show 4 / y = (y / 4)⁻¹ by simp [inv_div], Real.inv_rpow hq.le]
  field_simp

/-- The mixed derivative of the area-weighted kernel, with the constant curvature scale explicit. -/
theorem ds_mixed_product_rule {H T κ y u v : ℝ} {U : ℝ → ℝ}
    (hH : 0 < H) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) (huT : u < T) (hvT : v < T)
    (hU : ∀ t > 0, DifferentiableAt ℝ U t)
    (hU' : DifferentiableAt ℝ (deriv U) (dsChord T y u v)) :
    let s := dsChord T y u v
    deriv (fun x => deriv (fun z =>
      (x * dsOmega H T x) ^ κ * (z * dsOmega H T z) ^ κ *
        dsChord T y x z ^ (-κ) * U (dsChord T y x z)) v) u =
      H ^ (-2 * κ) * (4 / y) ^ κ *
        (deriv (dsMobius T) u * deriv (dsMobius T) v / (dsMobius T u * dsMobius T v)) *
          (s ^ 2 * deriv (deriv U) s + s * deriv U s) := by
  dsimp only
  let C := H ^ (-2 * κ) * (4 / y) ^ κ
  have hfv : 0 < dsMobius T v := div_pos hv (sub_pos.mpr hvT)
  have hfu : 0 < dsMobius T u := div_pos hu (sub_pos.mpr huT)
  have hq : 0 < y / 4 := by positivity
  have hv' := ds_mobius_hasDerivAt hvT
  have hu' := ds_mobius_hasDerivAt huT
  have he : (fun x => deriv (fun z =>
      (x * dsOmega H T x) ^ κ * (z * dsOmega H T z) ^ κ *
        dsChord T y x z ^ (-κ) * U (dsChord T y x z)) v) =ᶠ[𝓝 u]
      (fun x => C * ((deriv U (dsChord T y x v)) * ((y / 4) * dsMobius T x *
        (T / (T - v) ^ 2)))) := by
    filter_upwards [lt_mem_nhds hu, gt_mem_nhds huT] with x hx hxT
    have heq : (fun z =>
      (x * dsOmega H T x) ^ κ * (z * dsOmega H T z) ^ κ *
        dsChord T y x z ^ (-κ) * U (dsChord T y x z)) =ᶠ[𝓝 v]
        (fun z => C * U (dsChord T y x z)) := by
      filter_upwards [lt_mem_nhds hv, gt_mem_nhds hvT] with z hz hzT
      rw [ds_weight_cancel hH hy hx hz hxT hzT]
    have hpos : 0 < dsChord T y x v := mul_pos (mul_pos hq (div_pos hx (sub_pos.mpr hxT))) hfv
    have hs := hv'.const_mul ((y / 4) * dsMobius T x)
    exact heq.deriv_eq.trans (((hU _ hpos).hasDerivAt.comp v hs).const_mul C).deriv
  have hs : HasDerivAt (fun x => dsChord T y x v)
      (((y / 4) * (T / (T - u) ^ 2)) * dsMobius T v) u :=
    (hu'.const_mul (y / 4)).mul_const (dsMobius T v)
  have hd := ((hU'.hasDerivAt.comp u hs).mul
    ((hu'.const_mul (y / 4)).mul_const (T / (T - v) ^ 2))).const_mul C
  rw [he.deriv_eq]
  erw [hd.deriv]
  rw [hu'.deriv, hv'.deriv]
  simp only [Function.comp_apply]
  dsimp [dsChord, C]
  field_simp

/-- The hypergeometric differential operator on the normalized Bunch–Davies kernel. -/
def bdODE (κ e : ℝ) (Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * (1 - s) * deriv (deriv Y) s + (1 - κ - 2 * s) * deriv Y s - e * Y s
theorem bdODE_conformal_constant (κ s : ℝ) :
    bdODE κ 0 (fun _ => 1) s = 0 := by
  simp [bdODE, show (deriv (fun _ : ℝ => (1 : ℝ))) = fun _ => 0 by ext; simp]

/-- The conformal locus expressed through the bare mass and curvature coupling. -/
theorem bd_conformal_parameter_eq (D : ℕ) (hD : 4 ≤ D) {H : ℝ} (hH : 0 < H)
    (m ξ : ℝ) :
    let κ := ((D : ℝ) - 2) / 2
    (m ^ 2 + ξ * deSitterRicciScalar D H - κ * (κ + 1) * H ^ 2) / H ^ 2 = 0 ↔
      m ^ 2 + (ξ - deSitterConformalCoupling D) * deSitterRicciScalar D H = 0 := by
  dsimp only
  rw [div_eq_zero_iff, or_iff_left (pow_ne_zero _ hH.ne')]
  simpa [deSitterConformalMassSq] using congrArg (· = 0)
    (deSitterConformalMassSq_eq_sub D hD m ξ H)

open PowerSeries
open scoped PowerSeries

/-- The same differential operator acting coefficientwise on real formal power series. -/
def bdFormalODE (κ e : ℝ) (Y : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  X * (d⁄dX (d⁄dX Y)) - X * (X * (d⁄dX (d⁄dX Y))) +
    (1 - κ) • (d⁄dX Y) - X * ((2 : ℝ) • (d⁄dX Y)) - e • Y

theorem bd_frobenius_recurrence (κ e : ℝ) (Y : ℝ⟦X⟧) :
    bdFormalODE κ e Y = 0 ↔ ∀ j : ℕ,
      ((j : ℝ) + 1) * ((j : ℝ) + 1 - κ) * coeff (j + 1) Y =
        ((j : ℝ) * ((j : ℝ) + 1) + e) * coeff j Y := by
  have h (j : ℕ) : coeff j (bdFormalODE κ e Y) =
      ((j : ℝ) + 1) * ((j : ℝ) + 1 - κ) * coeff (j + 1) Y -
        ((j : ℝ) * ((j : ℝ) + 1) + e) * coeff j Y := by
    rcases j with _ | _ | j <;>
      simp only [bdFormalODE, map_sub, map_add, coeff_zero_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_smul, smul_eq_mul, Nat.cast_zero, Nat.cast_succ] <;> ring
  constructor
  · intro hz j
    have hc := h j
    rw [hz, map_zero, eq_comm, sub_eq_zero] at hc
    exact hc
  · intro hr
    ext j
    rw [h, hr, sub_self, map_zero]

theorem bd_first_coefficient {κ e : ℝ} {Y : ℝ⟦X⟧} (hκ : κ ≠ 1)
    (h₀ : coeff 0 Y = 1) (hY : bdFormalODE κ e Y = 0) :
    coeff 1 Y = e / (1 - κ) := by
  have h := (bd_frobenius_recurrence κ e Y).mp hY 0
  simp [h₀] at h
  apply (eq_div_iff (sub_ne_zero.mpr hκ.symm)).2
  linarith only [h]
theorem bd_resonance {e : ℝ} {Y : ℝ⟦X⟧} (h₀ : coeff 0 Y = 1)
    (hY : bdFormalODE 1 e Y = 0) : e = 0 := by
  have h := (bd_frobenius_recurrence 1 e Y).mp hY 0
  simpa [h₀, eq_comm] using h

/-- The coefficient of the leading logarithmic correction of every normalized solution
at the four-dimensional resonance. -/
theorem bd_resonant_log_coefficient {e : ℝ} {Y : ℝ → ℝ}
    (hY : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ Y s)
    (hY' : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (deriv Y) s)
    (hODE : ∀ s ∈ Ioo (0 : ℝ) 1, bdODE 1 e Y s = 0)
    (hnormal : Tendsto Y (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun s => (Y s - 1) / (s * Real.log s)) (𝓝[>] 0) (𝓝 e) := by
  let p := fun s : ℝ => (1 - s) ^ 2
  have hp (s : ℝ) : HasDerivAt p (-2 * (1 - s)) s := by
    convert (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).pow 2) using 1
    · rfl
    · simp [id]
  have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  have he := hs.mono fun s h => (hp s).mul (hY' s h).hasDerivAt
  refine Omega.tendsto_sub_div_mul_log_of_weighted_deriv (p := p) (hs.mono hY) hnormal ?_
    (he.mono fun _ h => h.differentiableAt) ?_
  · have hp₀ : Continuous p := (continuous_const.sub continuous_id).pow _
    simpa [p] using hp₀.continuousAt (x := (0 : ℝ)) |>.continuousWithinAt (s := Ioi 0) |>.tendsto
  · have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hh : Tendsto (fun s => e * (1 - s) * Y s) (𝓝[>] 0) (𝓝 e) := by
      simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hx).const_mul e).mul hnormal
    refine Tendsto.congr' ?_ hh
    filter_upwards [hs, he] with s hs hd
    erw [hd.deriv]
    have h := hODE s hs
    unfold bdODE at h
    dsimp [p]
    linear_combination -(1 - s) * h

/-- Exact angular coefficient of the leading mixed kernel in positive harmonic degree. -/
def dsLeadingCoefficient (κ e T u v : ℝ) (ℓ : ℕ) : ℝ :=
  -(e / (4 * Real.pi)) * deriv (dsMobius T) u * deriv (dsMobius T) v /
    (((ℓ : ℝ) + κ - 1) * ((ℓ : ℝ) + κ))
/-- The leading angular coefficient obtained from the power and logarithmic moments. -/
theorem ds_leading_angular_coefficient_eq (e T u v : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ κ > 1, -(Real.Gamma κ / (4 * Real.pi ^ (κ + 1)) * e / (4 * (κ - 1))) *
        deriv (dsMobius T) u * deriv (dsMobius T) v * Omega.sphericalAngularMoment κ ℓ (1 - κ) =
      dsLeadingCoefficient κ e T u v ℓ) ∧
    (Real.Gamma 1 / (4 * Real.pi ^ (2 : ℝ)) * e / 4) *
      deriv (dsMobius T) u * deriv (dsMobius T) v * deriv (Omega.sphericalAngularMoment 1 ℓ) 0 =
        dsLeadingCoefficient 1 e T u v ℓ := by
  refine ⟨fun κ hκ => Omega.sphericalAngularCoefficient_power hκ e _ _ ℓ, ?_⟩
  simpa [dsLeadingCoefficient] using Omega.sphericalAngularCoefficient_log e
    (deriv (dsMobius T) u) (deriv (dsMobius T) v) ℓ hℓ

theorem ds_leading_coefficient_sign {κ e H T u v : ℝ} {ℓ : ℕ}
    (hκ : 1 ≤ κ) (hℓ : 1 ≤ ℓ) (hH : 0 < H) (hT : 0 < T) (hu : u < T) (hv : v < T) :
    (dsLeadingCoefficient κ e T u v ℓ = 0 ↔ e * H ^ 2 = 0) ∧
    (0 < dsLeadingCoefficient κ e T u v ℓ ↔ e * H ^ 2 < 0) ∧
    (dsLeadingCoefficient κ e T u v ℓ < 0 ↔ 0 < e * H ^ 2) := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hp : 0 < ((ℓ : ℝ) + κ - 1) * ((ℓ : ℝ) + κ) :=
    mul_pos (by linarith) (by linarith)
  have hu' := (sub_pos.mpr hu).ne'
  have hv' := (sub_pos.mpr hv).ne'
  let a := (4 * Real.pi)⁻¹ * (T / (T - u) ^ 2) * (T / (T - v) ^ 2) *
    (((ℓ : ℝ) + κ - 1) * ((ℓ : ℝ) + κ))⁻¹
  have he : dsLeadingCoefficient κ e T u v ℓ = -e * a := by
    rw [dsLeadingCoefficient, (ds_mobius_hasDerivAt hu).deriv, (ds_mobius_hasDerivAt hv).deriv]
    simp only [a, div_eq_mul_inv]
    ring
  have hf : 0 < a := by dsimp [a]; positivity
  have hH' : 0 < H ^ 2 := sq_pos_of_pos hH
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_eq_zero, or_iff_left hf.ne', neg_eq_zero, mul_eq_zero, or_iff_left hH'.ne']
  · rw [mul_pos_iff_of_pos_right hf]
    rw [show (e * H ^ 2 < 0) ↔ 0 < -(e * H ^ 2) from neg_pos.symm,
      ← neg_mul, mul_pos_iff_of_pos_right hH']
  · rw [← neg_pos, ← neg_mul, neg_neg, mul_pos_iff_of_pos_right hf, mul_pos_iff_of_pos_right hH']

/-- At the conformal parameters, the spacelike hypergeometric kernel equals the conformal power
with its exact normalization. -/
theorem bd_conformal_hypergeometric {κ H s : ℝ} (hκ : 0 < κ) (hs : 0 < s) (hs₁ : s < 1) :
    H ^ (2 * κ) * Real.Gamma κ * Real.Gamma (κ + 1) /
        ((4 * Real.pi) ^ (κ + 1) * Real.Gamma (κ + 1)) *
          ordinaryHypergeometric κ (κ + 1) (κ + 1) (1 - s) =
      H ^ (2 * κ) * Real.Gamma κ / (4 * Real.pi) ^ (κ + 1) * s ^ (-κ) := by
  have hh := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -κ)
  have hn (j : ℕ) : (j : ℝ) ≠ -(κ + 1) := by
    have hj : (0 : ℝ) ≤ j := by positivity
    linarith
  rw [binomialSeries_eq_ordinaryHypergeometricSeries hn, neg_neg] at hh
  have hmem : s - 1 ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_neg (sub_neg.mpr hs₁)]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  have hsum := hh.hasSum hmem
  have hsum' : ordinaryHypergeometric κ (κ + 1) (κ + 1) (1 - s) = s ^ (-κ) := by
    convert hsum.tsum_eq using 1
    · unfold ordinaryHypergeometric FormalMultilinearSeries.sum
      congr 1
      funext j
      simp [FormalMultilinearSeries.compContinuousLinearMap]
    · rw [show 1 + (0 + (s - 1)) = s by ring]
  rw [hsum']
  have hΓ := (Real.Gamma_pos_of_pos (show 0 < κ + 1 by linarith)).ne'
  field_simp

private theorem ds_antipodal_base_pos {P : ℝ} (hP : P ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - P ^ 2 := by
  have ha : 0 < 1 + P := by linarith [hP.1]
  have hb : 0 < 1 - P := by linarith [hP.2]
  nlinarith [mul_pos ha hb]

/-- The invariant massless equation fixes the derivative up to one constant. A nonzero constant
forces a divergent derivative and excludes any finite one-sided limit at the antipode. -/
theorem allen_folacci_antipodal_obstruction {D : ℕ} (hD : 4 ≤ D) (W : ℝ → ℝ)
    (hW : ∀ P ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ W P)
    (hW' : ∀ P ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ (deriv W) P)
    (hODE : ∀ P ∈ Ioo (-1 : ℝ) 1,
      (1 - P ^ 2) * deriv (deriv W) P - (D : ℝ) * P * deriv W P = 0) :
    ∃ C : ℝ, (∀ P ∈ Ioo (-1 : ℝ) 1, deriv W P = C * (1 - P ^ 2) ^ (-(D : ℝ) / 2)) ∧
      (C ≠ 0 → Tendsto (fun P => |deriv W P|) (𝓝[Ioo (-1 : ℝ) 1] (-1)) atTop ∧
        ∀ a : ℝ, ¬ Tendsto W (𝓝[Ioo (-1 : ℝ) 1] (-1)) (𝓝 a)) := by
  let d : ℝ := (D : ℝ) / 2
  let I := Ioo (-1 : ℝ) 1
  let p := fun P : ℝ => 1 - P ^ 2
  have hd : 2 ≤ d := by
    have h : (4 : ℝ) ≤ D := by exact_mod_cast hD
    dsimp [d]
    linarith
  let f := fun P => p P ^ d * deriv W P
  have hf (P : ℝ) (hP : P ∈ I) : HasDerivAt f 0 P := by
    have hp : 0 < p P := ds_antipodal_base_pos hP
    have hp' : HasDerivAt p (-(2 * P)) P := by
      convert (hasDerivAt_const P (1 : ℝ)).sub ((hasDerivAt_id P).pow 2) using 1
      · rfl
      · simp
    convert (hp'.rpow_const (Or.inl hp.ne')).mul (hW' P hP).hasDerivAt using 1
    have he : p P ^ d = p P ^ (d - 1) * p P := by
      calc
        p P ^ d = p P ^ (d - 1 + 1) := by congr 1; ring
        _ = p P ^ (d - 1) * p P := by rw [Real.rpow_add hp, Real.rpow_one]
    rw [he]
    have hh := hODE P hP
    change p P * deriv (deriv W) P - (D : ℝ) * P * deriv W P = 0 at hh
    dsimp [d]
    linear_combination -p P ^ ((D : ℝ) / 2 - 1) * hh
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (-1 : ℝ) 1).isPreconnected (fun P hP => (hf P hP).differentiableAt.differentiableWithinAt)
    (fun P hP => (hf P hP).deriv)
  have hC' (P : ℝ) (hP : P ∈ I) : deriv W P = C * p P ^ (-d) := by
    have hm := hC P hP
    change p P ^ d * deriv W P = C at hm
    have hp : 0 < p P := ds_antipodal_base_pos hP
    rw [← hm, Real.rpow_neg hp.le]
    field_simp [(Real.rpow_pos_of_pos hp d).ne']
  have hdomain : ∀ᶠ P in 𝓝[I] (-1), P ∈ I := self_mem_nhdsWithin
  have hp₀ : Tendsto p (𝓝[I] (-1)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hdomain.mono fun P hP => ds_antipodal_base_pos hP⟩
    have hc : Continuous p := continuous_const.sub (continuous_id.pow 2)
    have := hc.continuousAt (x := (-1 : ℝ))
    change Tendsto p (𝓝 (-1)) (𝓝 (p (-1))) at this
    simpa [p] using this.mono_left nhdsWithin_le_nhds
  refine ⟨C, fun P hP => by simpa [p, d, neg_div] using hC' P hP, fun hne => ⟨?_, ?_⟩⟩
  · refine Tendsto.congr' (hdomain.mono fun P hP => ?_)
      (((tendsto_rpow_neg_nhdsGT_zero (show -d < 0 by linarith)).comp hp₀).const_mul_atTop
        (abs_pos.mpr hne))
    change |C| * p P ^ (-d) = |deriv W P|
    rw [hC' P hP, abs_mul, abs_of_nonneg (Real.rpow_nonneg (ds_antipodal_base_pos hP).le _)]
  · intro a ha
    let F := fun P => W P / C
    have hF (P : ℝ) (hP : P ∈ I) : HasDerivAt F (p P ^ (-d)) P := by
      convert (hW P hP).hasDerivAt.div_const C using 1
      rw [hC' P hP]
      field_simp
    have hab : (-1 : ℝ) < -1 / 2 := by norm_num
    apply Omega.no_finite_limit_of_reciprocal_sq_le_deriv hab (c := 1 / 4) (F := F)
      (by norm_num) (fun P hP => (hF P ⟨hP.1, by linarith [hP.2]⟩).differentiableAt)
      _ (a / C) ?_
    · intro P hP
      have hP' : P ∈ I := ⟨hP.1, by linarith [hP.2]⟩
      have hp : 0 < p P := ds_antipodal_base_pos hP'
      have hp1 : p P ≤ 1 := by dsimp [p]; nlinarith
      have hb : p P ≤ 2 * (1 + P) := by dsimp [p]; nlinarith [sq_nonneg (1 + P)]
      have hpow : p P ^ d ≤ (2 * (1 + P)) ^ 2 := calc
        p P ^ d ≤ p P ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hp hp1 hd
        _ ≤ _ := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact pow_le_pow_left₀ hp.le hb 2
      rw [show (2 * (1 + P)) ^ 2 = 4 * (P - (-1)) ^ 2 by ring] at hpow
      rw [(hF P hP').deriv, Real.rpow_neg hp.le]
      simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
        inv_anti₀ (Real.rpow_pos_of_pos hp d) hpow
    · rw [← nhdsWithin_Ioo_eq_nhdsGT (show (-1 : ℝ) < 1 by norm_num)]
      exact ha.div_const C

private theorem ds_unscaled_deriv {κ T u : ℝ} (hu : 0 < u) (huT : u < T) :
    deriv (fun x : ℝ => x ^ (1 - κ) / (T - x)) u =
      u ^ (-κ) * (((1 - κ) * T + κ * u) / (T - u) ^ 2) := by
  have hbase : HasDerivAt (fun x : ℝ => T - x) (-1) u := by
    convert (hasDerivAt_const u T).sub (hasDerivAt_id u) using 1
    · rfl
    · norm_num
  have h : HasDerivAt (fun x : ℝ => x ^ (1 - κ) / (T - x)) _ u :=
    (Real.hasDerivAt_rpow_const (p := 1 - κ) (Or.inl hu.ne')).div hbase (sub_pos.mpr huT).ne'
  rw [h.deriv]
  rw [show 1 - κ - 1 = -κ by ring, show 1 - κ = -κ + 1 by ring,
    Real.rpow_add hu, Real.rpow_one]
  ring

/-- The signed leading unscaled derivative has a quantitative lower bound near the tip. -/
theorem ds_unscaled_blowup {κ T u : ℝ} (hκ : 1 < κ) (hT : 0 < T) (hu : 0 < u)
    (huT : u < T) (hcut : κ * u ≤ (κ - 1) * T / 2) :
    (κ - 1) / (2 * T) * u ^ (-κ) ≤
      -deriv (fun x : ℝ => x ^ (1 - κ) / (T - x)) u := by
  rw [ds_unscaled_deriv hu huT]
  rw [← mul_neg, mul_comm ((κ - 1) / (2 * T)), ← neg_div]
  refine mul_le_mul_of_nonneg_left ((le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr huT))).2 ?_)
    (Real.rpow_nonneg hu.le _)
  have hden : (T - u) ^ 2 ≤ T ^ 2 := by
    nlinarith [mul_nonneg hu.le (show 0 ≤ 2 * T - u by linarith)]
  have hcoeff : 0 ≤ (κ - 1) / (2 * T) := by positivity
  calc
    (κ - 1) / (2 * T) * (T - u) ^ 2 ≤ (κ - 1) / (2 * T) * T ^ 2 :=
      mul_le_mul_of_nonneg_left hden hcoeff
    _ = (κ - 1) * T / 2 := by field_simp
    _ ≤ -((1 - κ) * T + κ * u) := by linarith

/-- In dimension five, the derivative vanishes at an interior point of the proposed interval. -/
theorem ds_unscaled_bound_counterexample {T : ℝ} (hT : 0 < T) :
    T / 3 ∈ Ioo (0 : ℝ) (T / 2) ∧
    |deriv (fun x : ℝ => x ^ (1 - (3 / 2 : ℝ)) / (T - x)) (T / 3)| <
      ((3 / 2 : ℝ) - 1) * (T / 3) ^ (-(3 / 2 : ℝ)) / T := by
  have hu : 0 < T / 3 := by positivity
  refine ⟨⟨hu, by linarith⟩, ?_⟩
  rw [ds_unscaled_deriv hu (by linarith),
    show (1 - (3 / 2 : ℝ)) * T + 3 / 2 * (T / 3) = 0 by ring, zero_div,
    mul_zero, abs_zero]
  positivity

/-- The affine radius of a modular coordinate in a diamond of radius `L`. -/
def dsModularRadius (L s : ℝ) : ℝ := L * Omega.logistic (2 * Real.pi) s

/-- The negative unscaled derivative multiplied by the modular Jacobian. -/
def dsUnscaledModularKernel (κ T L s : ℝ) : ℝ :=
  (2 * Real.pi * (dsModularRadius L s * (1 - Omega.logistic (2 * Real.pi) s))) *
    (-deriv (fun u : ℝ => u ^ (1 - κ) / (T - u)) (dsModularRadius L s))

private theorem ds_unscaled_modular_tendsto {κ T L : ℝ} (hκ : 1 < κ)
    (hL : 0 < L) (hLT : L < T) :
    Tendsto (dsUnscaledModularKernel κ T L) atBot atTop := by
  have hT : 0 < T := hL.trans hLT
  let δ := min T (((κ - 1) * T / 2) / κ)
  have hδ : 0 < δ := lt_min hT (by positivity)
  refine Omega.tendsto_logistic_jacobian_mul (by positivity : 0 < 2 * Real.pi)
    hL hκ (by positivity : 0 < (κ - 1) / (2 * T)) hδ
    (q := fun u => -deriv (fun x : ℝ => x ^ (1 - κ) / (T - x)) u) ?_
  intro u hu
  have hsmall := (le_div_iff₀ (by linarith : 0 < κ)).1
    (hu.2.le.trans (min_le_right T (((κ - 1) * T / 2) / κ)))
  exact ds_unscaled_blowup hκ hT hu.1 (hu.2.trans_le (min_le_left _ _))
    (by simpa only [mul_comm κ u] using hsmall)

private theorem ds_unscaled_modular_continuous {κ T L : ℝ} (hL : 0 < L) (hLT : L < T) :
    Continuous (dsUnscaledModularKernel κ T L) := by
  let p := Omega.logistic (2 * Real.pi)
  let u := dsModularRadius L
  have hp : Continuous p := continuous_iff_continuousAt.mpr fun s =>
    (Omega.hasDerivAt_logistic (2 * Real.pi) s).continuousAt
  have hu : Continuous u := hp.const_mul L
  apply continuous_iff_continuousAt.mpr
  intro s
  have hu_pos (t : ℝ) : 0 < u t := mul_pos hL (Real.sigmoid_pos _)
  have hu_lt (t : ℝ) : u t < T :=
    (mul_lt_of_lt_one_right hL (Real.sigmoid_lt_one _)).trans hLT
  have hd : ContinuousAt (fun t => deriv (fun x : ℝ => x ^ (1 - κ) / (T - x)) (u t)) s := by
    simp_rw [ds_unscaled_deriv (hu_pos _) (hu_lt _)]
    have hbase : Continuous (fun t => T - u t) := continuous_const.sub hu
    have hnum : Continuous (fun t => (1 - κ) * T + κ * u t) :=
      continuous_const.add (hu.const_mul κ)
    exact (hu.continuousAt.rpow_const (Or.inl (hu_pos s).ne')).mul
      (hnum.continuousAt.div (hbase.pow 2).continuousAt (pow_ne_zero _ (sub_pos.mpr (hu_lt s)).ne'))
  exact ((hu.mul (continuous_const.sub hp)).const_mul _).continuousAt.mul hd.neg

/-- Translation toward the tip makes the signed unscaled pairing diverge and preserves the
weighted Fourier square integral for every reference weight. -/
theorem ds_unscaled_packet_diverges {κ T L : ℝ} (hκ : 1 < κ)
    (hL : 0 < L) (hLT : L < T) {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g)
    (hgc : HasCompactSupport g) (hgn : 0 ≤ g) (hg0 : ∃ x, g x ≠ 0) :
    Tendsto (fun a : ℝ => ∫ s : ℝ, dsUnscaledModularKernel κ T L s * g (s + a)) atTop atTop ∧
      ∀ (w : ℝ → ℝ) (a : ℝ),
        (∫ ξ : ℝ, w ξ * ‖𝓕 (fun s : ℝ => (g (s + a) : ℂ)) ξ‖ ^ 2) =
        ∫ ξ : ℝ, w ξ * ‖𝓕 (fun s : ℝ => (g s : ℂ)) ξ‖ ^ 2 := by
  exact ⟨Omega.tendsto_integral_mul_translate (ds_unscaled_modular_continuous hL hLT)
    (ds_unscaled_modular_tendsto hκ hL hLT) hg.continuous hgc hgn hg0,
    Omega.integral_weighted_fourier_sq_translate (fun s => (g s : ℂ))⟩

end NullConeGravity
