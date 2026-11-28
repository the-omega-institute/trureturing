/- GID: D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horizon periodicity, thermal spectra, and Schwarzschild evaporation entropy. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Order.Field
import D5.S3.Analysis.ThermalIntegrals
import D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullModularKMSUniqueness

/-! In geometric units, the Euclidean horizon circle fixes the period and the
thermal flux gives a finite evaporation time with a positive entropy gain. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D

open BlackHoleThermodynamics4D

/-- Euclidean arc length along the fixed-radius orbit of the horizon time coordinate. -/
def euclideanCircumference (κ β ρ : ℝ) : ℝ :=
  ∫ s in 0..β, Real.sqrt
    (deriv (fun u : ℝ => ρ * Real.cos (κ * u)) s ^ 2 +
      deriv (fun u : ℝ => ρ * Real.sin (κ * u)) s ^ 2)

private theorem orbit_speed {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (s : ℝ) :
    Real.sqrt (deriv (fun u : ℝ => ρ * Real.cos (κ * u)) s ^ 2 +
      deriv (fun u : ℝ => ρ * Real.sin (κ * u)) s ^ 2) = ρ * κ := by
  have hx := ((hasDerivAt_const_mul (x := s) κ).cos).const_mul ρ
  have hy := ((hasDerivAt_const_mul (x := s) κ).sin).const_mul ρ
  rw [hx.deriv, hy.deriv]
  calc
    _ = Real.sqrt ((ρ * κ) ^ 2 *
        (Real.sin (κ * s) ^ 2 + Real.cos (κ * s) ^ 2)) := by
      congr 1
      ring
    _ = ρ * κ := by
      rw [Real.sin_sq_add_cos_sq, mul_one, Real.sqrt_sq (mul_pos hρ hκ).le]

theorem gibbons_hawking_conical_periodicity {κ β ρ : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hρ : 0 < ρ) :
    euclideanCircumference κ β ρ / (2 * Real.pi * ρ) = κ * β / (2 * Real.pi) ∧
    (euclideanCircumference κ β ρ / (2 * Real.pi * ρ) = 1 ↔ β = 2 * Real.pi / κ) ∧
    (β = 2 * Real.pi / κ ↔ 1 / β = hawkingTemp 1 κ) := by
  have hC : euclideanCircumference κ β ρ = β * (ρ * κ) := by
    unfold euclideanCircumference
    simp_rw [orbit_speed hκ hρ]
    simp [intervalIntegral.integral_const]
    ring
  have hr : euclideanCircumference κ β ρ / (2 * Real.pi * ρ) =
      κ * β / (2 * Real.pi) := by
    rw [hC]
    field_simp [hρ.ne', Real.pi_ne_zero]
  refine ⟨hr, ?_, ?_⟩
  · rw [hr, div_eq_iff (show (2 : ℝ) * Real.pi ≠ 0 by positivity), eq_div_iff hκ.ne']
    constructor <;> intro h <;> simpa [mul_comm] using h
  · unfold hawkingTemp
    rw [one_mul, eq_div_iff hκ.ne',
      div_eq_div_iff hβ.ne' (show (2 : ℝ) * Real.pi ≠ 0 by positivity)]
    constructor <;> intro h <;> linarith [mul_comm κ β]

private theorem rayleigh_jeans_limit {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun ω => ω / (Real.exp (β * ω) - 1)) (𝓝[>] 0) (𝓝 (1 / β)) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp (β * x)) β 0 := by
    simpa using (hasDerivAt_const_mul (x := (0 : ℝ)) β).exp
  have hs : Tendsto (fun x : ℝ => (Real.exp (β * x) - 1) / x) (𝓝[>] 0) (𝓝 β) := by
    refine (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2.congr ?_
    intro x
    simp [slope_def_field]
  simpa [one_div, inv_div] using hs.inv₀ hβ.ne'

private theorem wien_limit {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun ω => Real.exp (β * ω) * (1 / (Real.exp (β * ω) - 1))) atTop (𝓝 1) := by
  have hdecay : Tendsto (fun ω : ℝ => Real.exp (-(β * ω))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hβ))
  have hnear : Tendsto (fun ω : ℝ => 1 - Real.exp (-(β * ω))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hdecay (a := (1 : ℝ))
  have hlim := hnear.inv₀ one_ne_zero
  rw [inv_one] at hlim
  refine hlim.congr ?_
  intro ω
  have hden : 1 - Real.exp (-(β * ω)) =
      (Real.exp (β * ω) - 1) / Real.exp (β * ω) := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero _]
  rw [hden, inv_div, mul_one_div]

theorem bogoliubov_planck_and_fermi_dirac_spectra {β ω : ℝ} (hβ : 0 < β) (hω : 0 < ω) :
    (∀ A B : ℝ, A - B = 1 → A = Real.exp (β * ω) * B →
      B = 1 / (Real.exp (β * ω) - 1) ∧ 0 < B ∧
      A = Real.exp (β * ω) / (Real.exp (β * ω) - 1) ∧ A = 1 + B ∧
      B / (1 + B) = Real.exp (-(β * ω))) ∧
    (∀ A B : ℝ, A + B = 1 → A = Real.exp (β * ω) * B →
      B = 1 / (Real.exp (β * ω) + 1) ∧ 0 < B ∧ B < 1 / 2 ∧
      A = Real.exp (β * ω) / (Real.exp (β * ω) + 1) ∧ A = 1 - B ∧
      B / (1 - B) = Real.exp (-(β * ω)) ∧
      A = NullConeGravity.NullModularKMSUniqueness.thermal β ω) ∧
    Tendsto (fun x : ℝ => x / (Real.exp (β * x) - 1)) (𝓝[>] 0) (𝓝 (1 / β)) ∧
    Tendsto (fun x : ℝ => Real.exp (β * x) * (1 / (Real.exp (β * x) - 1))) atTop (𝓝 1) := by
  have hE : 1 < Real.exp (β * ω) := Real.one_lt_exp_iff.mpr (mul_pos hβ hω)
  have hminus : 0 < Real.exp (β * ω) - 1 := sub_pos.mpr hE
  have hplus : 0 < Real.exp (β * ω) + 1 := by linarith
  have hExp : Real.exp (β * ω) ≠ 0 := Real.exp_ne_zero _
  refine ⟨?_, ?_, rayleigh_jeans_limit hβ, wien_limit hβ⟩
  · intro A B hnorm hboltz
    have hb : B = 1 / (Real.exp (β * ω) - 1) :=
      (eq_div_iff hminus.ne').mpr (by rw [hboltz] at hnorm; linarith)
    have hp : 0 < B := hb.symm ▸ one_div_pos.mpr hminus
    have ha : A = 1 + B := by linarith
    refine ⟨hb, hp, ?_, ha, ?_⟩
    · rw [hboltz, hb, mul_one_div]
    · rw [← ha, hboltz, Real.exp_neg]
      field_simp [hExp, hp.ne']
  · intro A B hnorm hboltz
    have hb : B = 1 / (Real.exp (β * ω) + 1) :=
      (eq_div_iff hplus.ne').mpr (by rw [hboltz] at hnorm; linarith)
    have hp : 0 < B := hb.symm ▸ one_div_pos.mpr hplus
    have ha : A = 1 - B := by linarith
    have hbal : B = Real.exp (-(β * ω)) * A := by
      rw [hboltz, Real.exp_neg]
      field_simp [hExp]
    refine ⟨hb, hp, ?_, ?_, ha, ?_, ?_⟩
    · rw [hb, div_lt_div_iff₀ hplus (by norm_num : (0 : ℝ) < 2)]
      linarith
    · rw [hboltz, hb, mul_one_div]
    · rw [← ha, hbal]
      have hA : A ≠ 0 := hboltz.symm ▸ mul_ne_zero hExp hp.ne'
      field_simp [hA]
    · apply (NullConeGravity.NullModularKMSUniqueness.kms_normalized_symbol_unique β ω A).mp
      rw [show 1 - A = B by linarith]
      simpa only [neg_mul] using hbal

theorem stefan_boltzmann_4d_bose_and_fermi_integrals :
    (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1)) = Real.pi ^ 4 / 15 ∧
    (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x + 1)) = (7 / 8) * (Real.pi ^ 4 / 15) :=
  ⟨Omega.bose_einstein_cubic_integral, Omega.fermi_dirac_cubic_integral⟩

private theorem schwarzschild_area {M : ℝ} (hM : 0 ≤ M) :
    horizonArea M 0 0 = 16 * Real.pi * M ^ 2 := by
  simp [horizonArea, horizonFactor, rPlus, horizonGap, spin, Real.sqrt_sq hM]
  ring

private theorem schwarzschild_temperature {M : ℝ} (hM : 0 < M) :
    hawkingTemp 1 (surfaceGravity M 0 0) = 1 / (8 * Real.pi * M) := by
  simpa [schwarzschildTemp] using hawking_temp_schwarzschild (G := 1) (ℏ := 1) (by norm_num) hM

/-- Energy flux coefficient for one massless bosonic helicity. -/
def bosonicStefanBoltzmann : ℝ :=
  (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1)) / (8 * Real.pi ^ 2)

/-- Luminosity of an ideal black body with the Schwarzschild area and temperature. -/
def hawkingLuminosity (g M : ℝ) : ℝ :=
  g * bosonicStefanBoltzmann * horizonArea M 0 0 * (hawkingTemp 1 (surfaceGravity M 0 0)) ^ 4

theorem hawking_luminosity_inverse_square_law (g : ℝ) {M : ℝ} (hM : 0 < M) :
    hawkingTemp 1 (surfaceGravity M 0 0) = 1 / (8 * Real.pi * M) ∧
    hawkingLuminosity g M =
      g * (Real.pi ^ 2 / 120) * (16 * Real.pi * M ^ 2) * (1 / (8 * Real.pi * M)) ^ 4 ∧
    hawkingLuminosity g M = g / (30720 * Real.pi * M ^ 2) := by
  have ht := schwarzschild_temperature hM
  have hs : bosonicStefanBoltzmann = Real.pi ^ 2 / 120 := by
    rw [bosonicStefanBoltzmann, stefan_boltzmann_4d_bose_and_fermi_integrals.1]
    field_simp [Real.pi_ne_zero]
    ring
  have hL : hawkingLuminosity g M =
      g * (Real.pi ^ 2 / 120) * (16 * Real.pi * M ^ 2) * (1 / (8 * Real.pi * M)) ^ 4 := by
    rw [hawkingLuminosity, hs, schwarzschild_area hM.le, ht]
  refine ⟨ht, hL, ?_⟩
  rw [hL]
  field_simp [hM.ne', Real.pi_ne_zero]
  ring

def evapTime (M₀ α : ℝ) : ℝ := M₀ ^ 3 / (3 * α)

def evapMass (M₀ α t : ℝ) : ℝ :=
  M₀ * (1 - t / evapTime M₀ α) ^ (1 / 3 : ℝ)

private theorem evap_time_pos {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α) :
    0 < evapTime M₀ α := by
  unfold evapTime
  positivity

private theorem evap_base_pos {M₀ α t : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α)
    (ht : t < evapTime M₀ α) : 0 < 1 - t / evapTime M₀ α := by
  exact sub_pos.mpr ((div_lt_one (evap_time_pos hM₀ hα)).mpr ht)

private theorem evap_mass_pos {M₀ α t : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α)
    (ht : t < evapTime M₀ α) : 0 < evapMass M₀ α t :=
  mul_pos hM₀ (Real.rpow_pos_of_pos (evap_base_pos hM₀ hα ht) _)

private theorem evap_mass_zero (M₀ α : ℝ) : evapMass M₀ α 0 = M₀ := by
  simp [evapMass]

private theorem evap_mass_terminal {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α) :
    evapMass M₀ α (evapTime M₀ α) = 0 := by
  simp [evapMass, (evap_time_pos hM₀ hα).ne']

private theorem evap_mass_continuous (M₀ α : ℝ) : Continuous (evapMass M₀ α) :=
  (continuous_const.sub (continuous_id.div_const _)).rpow_const
    (fun _ => Or.inr (by norm_num)) |>.const_mul M₀

private theorem evap_mass_derivative {M₀ α t : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α)
    (ht : t < evapTime M₀ α) :
    HasDerivAt (evapMass M₀ α) (-α / (evapMass M₀ α t) ^ 2) t := by
  let b := 1 - t / evapTime M₀ α
  have hb : 0 < b := evap_base_pos hM₀ hα ht
  have hT : evapTime M₀ α ≠ 0 := (evap_time_pos hM₀ hα).ne'
  have hbase := (hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).div_const (evapTime M₀ α))
  have hd := ((Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hb.ne')).comp t
    hbase).const_mul M₀
  change HasDerivAt (evapMass M₀ α)
    (M₀ * ((1 / 3 : ℝ) * b ^ (1 / 3 - 1 : ℝ) * (0 - 1 / evapTime M₀ α))) t at hd
  have hp : b ^ (1 / 3 - 1 : ℝ) = ((b ^ (1 / 3 : ℝ)) ^ (2 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le, ← Real.rpow_neg hb.le]
    norm_num
  convert hd using 1
  rw [hp]
  change -α / (M₀ * b ^ (1 / 3 : ℝ)) ^ 2 = _
  rw [evapTime]
  have hpow : b ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  field_simp [hM₀.ne', hα.ne', hpow]
  ring

theorem hawking_evaporation_trajectory_and_runaway_heating {M₀ α : ℝ}
    (hM₀ : 0 < M₀) (hα : 0 < α) :
    evapMass M₀ α 0 = M₀ ∧
    (∀ t ∈ Ico 0 (evapTime M₀ α), 0 < evapMass M₀ α t ∧
      HasDerivAt (evapMass M₀ α) (-α / (evapMass M₀ α t) ^ 2) t) ∧
    Tendsto (evapMass M₀ α) (𝓝[<] evapTime M₀ α) (𝓝 0) ∧
    Tendsto (fun t => 1 / (8 * Real.pi * evapMass M₀ α t))
      (𝓝[<] evapTime M₀ α) atTop := by
  have hm : Tendsto (evapMass M₀ α) (𝓝[<] evapTime M₀ α) (𝓝 0) := by
    simpa only [evap_mass_terminal hM₀ hα] using
      (evap_mass_continuous M₀ α).continuousWithinAt (s := Iio (evapTime M₀ α))
        (x := evapTime M₀ α) |>.tendsto
  have hd : Tendsto (fun t => 8 * Real.pi * evapMass M₀ α t)
      (𝓝[<] evapTime M₀ α) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hm.const_mul (8 * Real.pi)
    · filter_upwards [self_mem_nhdsWithin (s := Iio (evapTime M₀ α))] with t ht
      change 0 < 8 * Real.pi * evapMass M₀ α t
      have hp := evap_mass_pos hM₀ hα ht
      positivity
  refine ⟨evap_mass_zero M₀ α, fun t ht => ⟨evap_mass_pos hM₀ hα ht.2,
    evap_mass_derivative hM₀ hα ht.2⟩, hm, ?_⟩
  simpa [Function.comp_def, one_div] using tendsto_inv_nhdsGT_zero.comp hd

/-- Entropy flux for isotropic massless radiation with pressure one third of the energy density. -/
def radiationEntropyFlux (P T : ℝ) : ℝ := (P + P / 3) / T

def hawkingPower (α M : ℝ) : ℝ := α / M ^ 2

def schwarzschildEntropy (M : ℝ) : ℝ := bekensteinEntropy 1 1 (horizonArea M 0 0)

def evaporationEntropyFlux (M₀ α t : ℝ) : ℝ :=
  radiationEntropyFlux (hawkingPower α (evapMass M₀ α t))
    (schwarzschildTemp 1 1 (evapMass M₀ α t))

private theorem schwarzschild_entropy {M : ℝ} (hM : 0 ≤ M) :
    schwarzschildEntropy M = 4 * Real.pi * M ^ 2 := by
  rw [schwarzschildEntropy, schwarzschild_area hM]
  unfold bekensteinEntropy
  ring

private theorem hawking_power_over_temp (α M : ℝ) :
    hawkingPower α M / schwarzschildTemp 1 1 M = 8 * Real.pi * α / M := by
  by_cases hm : M = 0
  · simp [hm, hawkingPower, schwarzschildTemp]
  · unfold hawkingPower schwarzschildTemp
    field_simp [hm, Real.pi_ne_zero]

private theorem evaporation_flux_eq (M₀ α t : ℝ) :
    evaporationEntropyFlux M₀ α t = (4 / 3) * (8 * Real.pi * α / evapMass M₀ α t) := by
  unfold evaporationEntropyFlux radiationEntropyFlux
  rw [← hawking_power_over_temp]
  ring

private theorem evaporation_entropy_derivative {M₀ α t : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α)
    (ht : t < evapTime M₀ α) :
    HasDerivAt (fun s => 4 * Real.pi * (evapMass M₀ α s) ^ 2)
      (-8 * Real.pi * α / evapMass M₀ α t) t := by
  have hm := (evap_mass_pos hM₀ hα ht).ne'
  have hd := ((evap_mass_derivative hM₀ hα ht).fun_pow 2).const_mul (4 * Real.pi)
  convert hd using 1
  field_simp [hm]
  ring

private theorem evaporation_flux_integrable {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α) :
    IntervalIntegrable (evaporationEntropyFlux M₀ α) volume 0 (evapTime M₀ α) := by
  let T := evapTime M₀ α
  have hT : 0 < T := evap_time_pos hM₀ hα
  have hi := intervalIntegral.intervalIntegrable_rpow'
    (a := 1) (b := 0) (r := (-1 / 3 : ℝ)) (by norm_num)
  have hj : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-1 / 3 : ℝ)) volume 0 1 := by
    simpa using hi.comp_sub_left 1
  have hk : IntervalIntegrable (fun t : ℝ => (1 - t / T) ^ (-1 / 3 : ℝ)) volume 0 T := by
    simpa [div_eq_inv_mul, hT.ne'] using hj.comp_mul_left (c := T⁻¹)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
  have ha := (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp
    (hk.const_mul ((4 / 3) * (8 * Real.pi * α / M₀)))
  refine ha.congr_fun (fun t ht => ?_) measurableSet_Icc
  have hb : 0 ≤ 1 - t / T := sub_nonneg.mpr ((div_le_one hT).mpr ht.2)
  dsimp only
  rw [evaporation_flux_eq, evapMass, show evapTime M₀ α = T by rfl,
    show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.rpow_neg hb]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem evaporation_entropy_integral {M₀ α : ℝ} (hM₀ : 0 < M₀) (hα : 0 < α) :
    (∫ t in 0..evapTime M₀ α, evaporationEntropyFlux M₀ α t) =
      (4 / 3) * schwarzschildEntropy M₀ := by
  have hT := evap_time_pos hM₀ hα
  have hd (t : ℝ) (ht : t ∈ Ioo 0 (evapTime M₀ α)) :
      HasDerivAt (fun s => -(4 / 3) * (4 * Real.pi * (evapMass M₀ α s) ^ 2))
        (evaporationEntropyFlux M₀ α t) t := by
    rw [evaporation_flux_eq]
    convert (evaporation_entropy_derivative hM₀ hα ht.2).const_mul (-(4 / 3)) using 1
    ring
  have hc : Continuous (fun s => -(4 / 3) * (4 * Real.pi * (evapMass M₀ α s) ^ 2)) :=
    (((evap_mass_continuous M₀ α).pow 2).const_mul (4 * Real.pi)).const_mul (-(4 / 3))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hc.continuousOn hd
    (evaporation_flux_integrable hM₀ hα), evap_mass_terminal hM₀ hα, evap_mass_zero,
    schwarzschild_entropy hM₀.le]
  ring

theorem zurek_generalized_second_law_irreversible_entropy_production {M₀ α : ℝ}
    (hM₀ : 0 < M₀) (hα : 0 < α) :
    (∀ t ∈ Ico 0 (evapTime M₀ α),
      let M := evapMass M₀ α t
      let P := hawkingPower α M
      let T := schwarzschildTemp 1 1 M
      schwarzschildEntropy M = 4 * Real.pi * M ^ 2 ∧
      HasDerivAt (fun s => 4 * Real.pi * (evapMass M₀ α s) ^ 2) (-P / T) t ∧
      -P / T = -8 * Real.pi * α / M ∧ -P / T < 0 ∧
      evaporationEntropyFlux M₀ α t = (4 / 3) * (P / T) ∧
      evaporationEntropyFlux M₀ α t + (-P / T) = (1 / 3) * (P / T) ∧
      (1 / 3) * (P / T) = (8 * Real.pi / 3) * (α / M) ∧
      0 < (1 / 3) * (P / T)) ∧
    IntervalIntegrable (evaporationEntropyFlux M₀ α) volume 0 (evapTime M₀ α) ∧
    (∫ t in 0..evapTime M₀ α, evaporationEntropyFlux M₀ α t) =
      (4 / 3) * schwarzschildEntropy M₀ ∧
    (∫ t in 0..evapTime M₀ α, evaporationEntropyFlux M₀ α t) - schwarzschildEntropy M₀ =
      (1 / 3) * schwarzschildEntropy M₀ ∧
    0 < (1 / 3) * schwarzschildEntropy M₀ := by
  have hi := evaporation_entropy_integral hM₀ hα
  refine ⟨?_, evaporation_flux_integrable hM₀ hα, hi, ?_, ?_⟩
  · intro t ht
    dsimp only
    have hm := evap_mass_pos hM₀ hα ht.2
    have he : -(hawkingPower α (evapMass M₀ α t)) /
        schwarzschildTemp 1 1 (evapMass M₀ α t) = -8 * Real.pi * α / evapMass M₀ α t := by
      rw [neg_div, hawking_power_over_temp]
      ring
    have hf : evaporationEntropyFlux M₀ α t =
        (4 / 3) * (hawkingPower α (evapMass M₀ α t) /
          schwarzschildTemp 1 1 (evapMass M₀ α t)) := by
      rw [evaporation_flux_eq, hawking_power_over_temp]
    refine ⟨schwarzschild_entropy hm.le, he.symm ▸ evaporation_entropy_derivative hM₀ hα ht.2,
      he, ?_, hf, ?_, ?_, ?_⟩
    · rw [he]
      have hn : (-8 : ℝ) * Real.pi * α < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hα
      exact div_neg_of_neg_of_pos hn hm
    · rw [hf, neg_div]
      ring
    · rw [hawking_power_over_temp]
      ring
    · rw [hawking_power_over_temp]
      positivity
  · rw [hi]
    ring
  · rw [schwarzschild_entropy hM₀.le]
    positivity

end D5.S3.Geometry.Lorentz.HawkingUnruhThermalRadiation4D
