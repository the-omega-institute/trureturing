/- GID: D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact de Sitter tensor modes, null-screen polarizations and joint dimension selection. -/

import D5.S3.Geometry.Lorentz.DimensionSelection4D
import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Quantum.Analysis.NullConeGravity.ConformalMaxwellSelection4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Weighted tensor mode equations, four-dimensional normalization, and null-screen ranks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NullConeGravity

open Filter Set
open scoped ComplexConjugate Topology
open D5.S3.Geometry.Lorentz
open D5.S3.Geometry.Lorentz.DimensionSelection4D

/-- Half the exponent of the quadratic tensor kinetic weight. -/
def gravitonKappa (D : ℕ) : ℝ := ((D : ℝ) - 2) / 2

/-- The spatial tensor equation has the minimally coupled massless scalar potential. -/
theorem ds_graviton_tt_rescaled_ode (D : ℕ) (hD : 2 ≤ D) {H t : ℝ}
    (hH : 0 < H) (ht : t < 0) (k : ℝ) (h : ℝ → ℝ)
    (hh : ∀ s < 0, DifferentiableAt ℝ h s) (hh' : DifferentiableAt ℝ (deriv h) t) :
    let Ω := Omega.inverseTimeScale H
    let v := fun s => Ω s ^ gravitonKappa D * h s
    deriv (fun s => Ω s ^ (D - 2) * deriv h s) t + Ω t ^ (D - 2) * k ^ 2 * h t =
      Ω t ^ gravitonKappa D *
        (deriv (deriv v) t + (k ^ 2 - gravitonKappa D * (gravitonKappa D + 1) / t ^ 2) * v t) := by
  dsimp only
  have hw {s : ℝ} (hs : s < 0) :
      (Omega.inverseTimeScale H s ^ gravitonKappa D) ^ 2 =
        Omega.inverseTimeScale H s ^ (D - 2) := by
    have hp : 0 < Omega.inverseTimeScale H s :=
      Omega.inverseTimeScale_pos hH hs
    rw [pow_two, ← Real.rpow_add hp, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hD]
    unfold gravitonKappa
    ring
  have hd : (fun s => Omega.inverseTimeScale H s ^ (D - 2) * deriv h s)
      =ᶠ[𝓝 t] (fun s => (Omega.inverseTimeScale H s ^ gravitonKappa D) ^ 2 * deriv h s) := by
    filter_upwards [Iio_mem_nhds ht] with s hs using congrArg (· * deriv h s) (hw hs).symm
  rw [hd.deriv_eq, ← hw ht]
  exact Omega.inverseTime_rescaled_ode hH ht (gravitonKappa D) h (fun _ => k ^ 2) hh hh'

/-- Zero scalar mass and curvature coupling give the same potential as the tensor equation. -/
theorem ds_graviton_tt_scalar_potential (D : ℕ) (hD : 4 ≤ D) {H t : ℝ}
    (hH : 0 < H) (ht : t < 0) (k : ℝ) :
    k ^ 2 + Omega.inverseTimeScale H t ^ 2 * deSitterConformalMassSq D 0 0 H =
      k ^ 2 - gravitonKappa D * (gravitonKappa D + 1) / t ^ 2 := by
  rw [← deSitterConformalMassSq_eq_sub D hD]
  unfold gravitonKappa Omega.inverseTimeScale
  field_simp [hH.ne', ht.ne]
  ring

/-- The canonically normalized positive-frequency mode in four dimensions. -/
def ds4GravitonBDMode (k t : ℝ) : ℂ :=
  Complex.exp (-(k : ℂ) * Complex.I * (t : ℂ)) *
    (1 - Complex.I / (k : ℂ) * (t : ℂ)⁻¹) / (Real.sqrt (2 * k) : ℂ)

private theorem bdMode_derivative (k : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (ds4GravitonBDMode k)
      (Complex.exp (-(k : ℂ) * Complex.I * (t : ℂ)) *
        (-(k : ℂ) * Complex.I * (1 - Complex.I / (k : ℂ) * (t : ℂ)⁻¹) +
          Complex.I / (k : ℂ) * ((t : ℂ)⁻¹) ^ 2) / (Real.sqrt (2 * k) : ℂ)) t := by
  let c : ℂ := -(k : ℂ) * Complex.I
  let q : ℂ := Complex.I / (k : ℂ)
  have hcast := (hasDerivAt_id t).ofReal_comp
  have hz : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have he := (hcast.const_mul c).cexp
  have hf := (hasDerivAt_const t (1 : ℂ)).sub ((hcast.inv (by simpa using hz)).const_mul q)
  convert (he.mul hf).div_const (Real.sqrt (2 * k) : ℂ) using 1
  · rfl
  · simp only [c, q, id_eq, Complex.ofReal_one, mul_one, Pi.sub_apply, Pi.inv_apply,
      zero_sub, mul_neg, div_eq_mul_inv, inv_pow]
    ring

/-- The normalized mode solves the exact tensor equation with curvature coefficient two. -/
theorem ds4_graviton_bd_mode_solves_ode {k t : ℝ} (hk : 0 < k) (ht : t < 0) :
    deriv (deriv (ds4GravitonBDMode k)) t +
      ((k : ℂ) ^ 2 - 2 / (t : ℂ) ^ 2) * ds4GravitonBDMode k t = 0 := by
  let c : ℂ := -(k : ℂ) * Complex.I
  let q : ℂ := Complex.I / (k : ℂ)
  let e : ℝ → ℂ := fun s => Complex.exp (c * (s : ℂ))
  let x : ℝ → ℂ := fun s => (s : ℂ)⁻¹
  let N : ℂ := Real.sqrt (2 * k)
  have hfirst : deriv (ds4GravitonBDMode k) =ᶠ[𝓝 t]
      fun s => e s * (c * (1 - q * x s) + q * x s ^ 2) / N := by
    filter_upwards [Iio_mem_nhds ht] with s hs using (bdMode_derivative k hs.ne).deriv
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne
  have hcast := (hasDerivAt_id t).ofReal_comp
  have he : HasDerivAt e (e t * c) t := by simpa [e, id_eq] using (hcast.const_mul c).cexp
  have hx : HasDerivAt x (-(x t ^ 2)) t := by
    convert hcast.inv (by simpa using htC) using 1
    · rfl
    · simp [x, id_eq, inv_pow, div_eq_mul_inv]
  have hf := ((hasDerivAt_const t (1 : ℂ)).sub (hx.const_mul q)).const_mul c
  have hd := ((he.mul (hf.add ((hx.pow 2).const_mul q))).div_const N).congr_of_eventuallyEq hfirst
  rw [hd.deriv]
  change (e t * c * (c * (1 - q * x t) + q * x t ^ 2) +
    e t * (c * (0 - q * -(x t ^ 2)) + q * (2 * x t ^ (2 - 1) * -(x t ^ 2)))) / N +
    ((k : ℂ) ^ 2 - 2 / (t : ℂ) ^ 2) * (e t * (1 - q * x t) / N) = 0
  have hcc : c * c = -(k : ℂ) ^ 2 := by
    dsimp [c]
    linear_combination (k : ℂ) ^ 2 * Complex.I_sq
  have hcq : c * q = 1 := by
    calc
      c * q = -((k : ℂ) * (k : ℂ)⁻¹) * (Complex.I * Complex.I) := by
        simp only [c, q, div_eq_mul_inv]
        ring
      _ = 1 := by rw [mul_inv_cancel₀ hkC, ← pow_two, Complex.I_sq]; norm_num
  have hcancel : c * (c * (1 - q * x t) + q * x t ^ 2) +
      (c * (0 - q * -(x t ^ 2)) + q * (2 * x t ^ (2 - 1) * -(x t ^ 2))) +
      ((k : ℂ) ^ 2 - 2 / (t : ℂ) ^ 2) * (1 - q * x t) = 0 := by
    simp only [show 2 - 1 = 1 by decide, pow_one, zero_sub, mul_neg, neg_neg]
    simp only [x, inv_pow, div_eq_mul_inv] at *
    linear_combination (1 - q * (t : ℂ)⁻¹) * hcc + 2 * ((t : ℂ)⁻¹) ^ 2 * hcq
  linear_combination (e t / N) * hcancel

/-- The constant Wronskian, with conformal time increasing to the future. -/
theorem ds4_graviton_bd_wronskian {k t : ℝ} (hk : 0 < k) (ht : t < 0) :
    ds4GravitonBDMode k t * conj (deriv (ds4GravitonBDMode k) t) -
      conj (ds4GravitonBDMode k t) * deriv (ds4GravitonBDMode k) t = Complex.I := by
  rw [(bdMode_derivative k ht.ne).deriv]
  unfold ds4GravitonBDMode
  let z : ℂ := -(k : ℂ) * Complex.I * (t : ℂ)
  let N : ℂ := Real.sqrt (2 * k)
  have hN : N ^ 2 = 2 * (k : ℂ) := by
    change ((Real.sqrt (2 * k) : ℝ) : ℂ) ^ 2 = _
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 2 * k by positivity)
  have hN0 : N ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity : 0 < 2 * k)).ne'
  have hphase : Complex.exp z * conj (Complex.exp z) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, show z + conj z = 0 by simp [z],
      Complex.exp_zero]
  let f : ℂ := 1 - Complex.I / (k : ℂ) * (t : ℂ)⁻¹
  let g : ℂ := -(k : ℂ) * Complex.I * f + Complex.I / (k : ℂ) * ((t : ℂ)⁻¹) ^ 2
  change Complex.exp z * f / N * conj (Complex.exp z * g / N) -
    conj (Complex.exp z * f / N) * (Complex.exp z * g / N) = Complex.I
  have hconj : conj N = N := Complex.conj_ofReal _
  rw [map_div₀, map_div₀, map_mul, map_mul, hconj]
  calc
    _ = (Complex.exp z * conj (Complex.exp z)) * (f * conj g - conj f * g) / N ^ 2 := by
      field_simp [hN0]
    _ = Complex.I := by
      rw [hphase, one_mul, div_eq_iff (pow_ne_zero _ hN0), hN]
      have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
      have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne
      dsimp [f, g]
      simp only [map_add, map_sub, map_neg, map_mul, map_div₀, map_inv₀, map_pow,
        Complex.conj_ofReal, Complex.conj_I, map_one]
      field_simp [hk', ht']
      linear_combination (-2 * (k : ℂ) * (t : ℂ)) * Complex.I_sq

/-- The squared metric amplitude at finite negative time. -/
theorem ds4_graviton_bd_power {H k t : ℝ} (hH : 0 < H) (hk : 0 < k) (ht : t < 0) :
    ‖ds4GravitonBDMode k t / (Omega.inverseTimeScale H t : ℂ)‖ ^ 2 =
      H ^ 2 / (2 * k ^ 3) * (1 + k ^ 2 * t ^ 2) := by
  have he : ‖Complex.exp (-(k : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [← Complex.normSq_eq_norm_sq]
  unfold ds4GravitonBDMode
  rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_eq_norm_sq
    (Complex.exp _), he]
  simp only [one_pow, one_mul, Complex.normSq_ofReal]
  have hf : Complex.normSq (1 - Complex.I / (k : ℂ) * (t : ℂ)⁻¹) =
      1 + (k * t)⁻¹ ^ 2 := by
    have hmul : Complex.I / (k : ℂ) * (t : ℂ)⁻¹ = ((k * t)⁻¹ : ℝ) * Complex.I := by
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hmul]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  rw [hf]
  unfold Omega.inverseTimeScale
  field_simp [hH.ne', hk.ne', ht.ne]
  rw [Real.sq_sqrt (by positivity : 0 ≤ k * 2)]
  ring

/-- The finite late-time power is reached from negative conformal times. -/
theorem ds4_graviton_bd_superhorizon_limit {H k : ℝ} (hH : 0 < H) (hk : 0 < k) :
    Tendsto (fun t : ℝ => ‖ds4GravitonBDMode k t / (Omega.inverseTimeScale H t : ℂ)‖ ^ 2)
      (𝓝[<] (0 : ℝ)) (𝓝 (H ^ 2 / (2 * k ^ 3))) := by
  have he : (fun t : ℝ => ‖ds4GravitonBDMode k t / (Omega.inverseTimeScale H t : ℂ)‖ ^ 2)
      =ᶠ[𝓝[<] (0 : ℝ)] fun t => H ^ 2 / (2 * k ^ 3) * (1 + k ^ 2 * t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht using ds4_graviton_bd_power hH hk ht
  have hc : Continuous (fun t : ℝ => H ^ 2 / (2 * k ^ 3) * (1 + k ^ 2 * t ^ 2)) := by
    fun_prop
  have hlim := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
  simpa using hlim.congr' he.symm

/-- The transverse-traceless tensor space in spacetime dimension D has a screen of size D − 2. -/
abbrev GravitonTT (D : ℕ) := ScreenSTF D

/-- The number of graviton polarizations from the transverse screen. -/
def gravitonPolarizationCount (D : ℕ) : ℕ := (D - 2) * (D - 1) / 2 - 1

theorem gravitonPolarization_eq_screenSTF (D : ℕ) :
    gravitonPolarizationCount D = screenDim D := by
  unfold gravitonPolarizationCount screenDim
  by_cases hD : 3 ≤ D
  · have h : (D - 2) * (D - 1) = D * (D - 3) + 2 := by
      zify [hD, show 2 ≤ D by omega, show 1 ≤ D by omega]
      ring
    omega
  · interval_cases D <;> decide

theorem finrank_gravitonTT (D : ℕ) (hD : 2 ≤ D) :
    Module.finrank ℝ (GravitonTT D) = (D - 2) * (D - 1) / 2 - 1 := by
  change Module.finrank ℝ (ScreenSTF D) = gravitonPolarizationCount D
  rw [gravitonPolarization_eq_screenSTF]
  by_cases h : 3 ≤ D
  · exact finrank_screenSTF D h
  · have h₂ : D = 2 := by omega
    subst D
    have : IsEmpty (Sym2 (Fin 0)) := ⟨fun a => Sym2.ind (fun i _ => Fin.elim0 i) a⟩
    have : Subsingleton (ScreenSTF 2) := ⟨fun A B =>
      Subtype.ext (funext fun p => isEmptyElim p)⟩
    exact Module.finrank_zero_of_subsingleton

theorem graviton_polarizations_three_four_five :
    gravitonPolarizationCount 3 = 0 ∧ gravitonPolarizationCount 4 = 2 ∧
      gravitonPolarizationCount 5 = 5 := by decide

/-- A four-dimensional Weyl tide has the two real coordinates of the tensor screen. -/
theorem graviton4_weyl_screen_coordinates (C : WeylNullScreen.Weyl4)
    (r : WeylNullScreen.FutureNullRay) :
    let T := fun a b => WeylNullScreen.tidal C.val (WeylNullScreen.nullGenerator r)
      (WeylNullScreen.screenFrame r a) (WeylNullScreen.screenFrame r b)
    (WeylNullScreen.complexTide C.val r).re / 2 = T 0 0 ∧
      (WeylNullScreen.complexTide C.val r).im / 2 = T 0 1 := by
  dsimp only
  rw [WeylNullScreen.complexTide_weyl]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]

theorem graviton_propagating_iff (D : ℕ) : 0 < gravitonPolarizationCount D ↔ 4 ≤ D := by
  rw [gravitonPolarization_eq_screenSTF, screenDim_pos_iff]

theorem scalar_nullDiamond_and_propagating_gravity_iff (D : ℕ) :
    (4 ≤ D ∧ Summable (leadingModeWeight D)) ↔ D = 4 ∨ D = 5 := by
  have hs (hD : 4 ≤ D) : Summable (leadingModeWeight D) ↔ D = 4 ∨ D = 5 := by
    rw [← summable_nat_add_iff 1 (f := leadingModeWeight D)]
    have h := leadingModeWeight_summable_iff D hD
    rw [← summable_nat_add_iff 1] at h
    simpa only [Nat.add_one_ne_zero, ite_false] using h
  refine ⟨fun h => (hs h.1).mp h.2, fun h => ?_⟩
  have hD : 4 ≤ D := by omega
  exact ⟨hD, (hs hD).mpr h⟩

theorem unique_dimension_four_of_nullDiamond_and_conformalMaxwell (D : ℕ) :
    (4 ≤ D ∧ Summable (leadingModeWeight D) ∧
      (∀ Ω : ℝ, 0 < Ω → maxwellConformalWeight D Ω = 1)) ↔ D = 4 := by
  rw [maxwellConformalWeight_eq_one_iff]
  refine ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨hD, hs⟩ := (scalar_nullDiamond_and_propagating_gravity_iff D).mpr (Or.inl h)
  exact ⟨hD, hs, h⟩

theorem unique_dimension_four_of_graviton_nullDiamond_and_procaConformal (D : ℕ) :
    (0 < gravitonPolarizationCount D ∧ Summable (leadingModeWeight D) ∧
      procaCurvaturePotential D = 0) ↔ D = 4 := by
  rw [graviton_propagating_iff]
  refine ⟨fun h => (proca_curvature_potential_zero_iff D (by omega)).mp h.2.2, fun h => ?_⟩
  obtain ⟨hD, hs⟩ := (scalar_nullDiamond_and_propagating_gravity_iff D).mpr (Or.inl h)
  exact ⟨hD, hs, (proca_curvature_potential_zero_iff D (by omega)).mpr h⟩

/-- The Weyl, leading angular, Maxwell and Hodge criteria on the same spacetime dimension. -/
theorem grand_unification_unique_dimension_four (D : ℕ) (hD : 3 ≤ D) :
    (0 < Module.finrank ℝ (Weyl D) ∧ Summable (leadingModeWeight D) ∧
      (∀ Ω : ℝ, 0 < Ω → maxwellConformalWeight D Ω = 1) ∧ D - 2 = 2) ↔ D = 4 := by
  rw [weylDim_pos_iff D hD]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs := (scalar_nullDiamond_and_propagating_gravity_iff D).mp ⟨h.1, h.2.1⟩
    exact (unique_dimension_four_of_weyl_modular_hodge D).mp
      ⟨(screenDim_pos_iff D).mpr h.1, (summable_angularMode_iff D).mpr (by omega), h.2.2.2⟩
  · obtain ⟨hg, hs, hm⟩ := (unique_dimension_four_of_nullDiamond_and_conformalMaxwell D).mpr h
    exact ⟨hg, hs, hm, (hodge_two_form_degree_iff D).mpr h⟩

end NullConeGravity
