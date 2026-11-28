/- GID: D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyon energy, the exact radial monopole mass and modular invariance of the charge lattice. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! The Euclidean energy completion applies to any finite family of field
components. The exact mass uses the dimensionless spherical profiles and their
boundary energy. Electric and magnetic charge transport preserves the
antisymmetric pairing and compensates for the change of complex coupling. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D

section Energy

variable {ι : Type*} [Fintype ι]

def fieldDot (u v : ι → ℝ) : ℝ := ∑ k, u k * v k

def fieldNormSq (u : ι → ℝ) : ℝ := fieldDot u u

def ymhEnergyDensity (E B DPhi : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (fieldNormSq E + fieldNormSq B + fieldNormSq DPhi)

private theorem fieldNormSq_nonneg (u : ι → ℝ) : 0 ≤ fieldNormSq u :=
  Finset.sum_nonneg fun k _ ↦ mul_self_nonneg (u k)

private theorem fieldNormSq_eq_zero (u : ι → ℝ) : fieldNormSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hz := (Fintype.sum_eq_zero_iff_of_nonneg (fun k ↦ mul_self_nonneg (u k))).mp h
    funext k
    exact mul_self_eq_zero.mp (congrFun hz k)
  · rintro rfl
    simp [fieldNormSq, fieldDot]

theorem bogomolny_dyon_completion (E B DPhi : ι → ℝ) (α : ℝ) :
    ymhEnergyDensity E B DPhi =
      (1 / 2) * fieldNormSq (fun k ↦ E k - Real.sin α * DPhi k) +
      (1 / 2) * fieldNormSq (fun k ↦ B k - Real.cos α * DPhi k) +
      Real.sin α * fieldDot E DPhi + Real.cos α * fieldDot B DPhi := by
  unfold ymhEnergyDensity fieldNormSq fieldDot
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun x : ℝ ↦ (1 / 2) * DPhi k ^ 2 * x) (Real.sin_sq_add_cos_sq α)
  linarith only [h]

private theorem exists_angle_of_unit (s c : ℝ) (h : s ^ 2 + c ^ 2 = 1) :
    ∃ α : ℝ, Real.sin α = s ∧ Real.cos α = c := by
  have hs : -1 ≤ s ∧ s ≤ 1 := by
    constructor
    · by_contra! hlt
      nlinarith [sq_nonneg c, mul_pos (show 0 < -1 - s by linarith)
        (show 0 < 1 - s by linarith)]
    · by_contra! hgt
      nlinarith [sq_nonneg c, mul_pos (show 0 < s - 1 by linarith)
        (show 0 < s + 1 by linarith)]
  have hcos : Real.cos (Real.arcsin s) = |c| := by
    rw [Real.cos_arcsin, show 1 - s ^ 2 = c ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  by_cases hc : 0 ≤ c
  · exact ⟨Real.arcsin s, Real.sin_arcsin hs.1 hs.2, hcos.trans (abs_of_nonneg hc)⟩
  · refine ⟨Real.pi - Real.arcsin s, ?_, ?_⟩
    · rw [Real.sin_pi_sub, Real.sin_arcsin hs.1 hs.2]
    · rw [Real.cos_pi_sub, hcos, abs_of_neg (lt_of_not_ge hc), neg_neg]

private theorem sqrt_charge_attained (x y : ℝ) :
    ∃ α : ℝ, Real.sin α * x + Real.cos α * y = Real.sqrt (x ^ 2 + y ^ 2) := by
  set r := Real.sqrt (x ^ 2 + y ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  by_cases hz : r = 0
  · have hx : x = 0 := by rw [hz] at hrSq; nlinarith [sq_nonneg y]
    have hy : y = 0 := by rw [hz] at hrSq; nlinarith [sq_nonneg x]
    exact ⟨0, by rw [hx, hy, hz]; simp⟩
  have hu : (x / r) ^ 2 + (y / r) ^ 2 = 1 := by
    field_simp [hz]
    linarith
  obtain ⟨α, hs, hc⟩ := exists_angle_of_unit _ _ hu
  refine ⟨α, ?_⟩
  rw [hs, hc]
  rw [show x / r * x + y / r * y = (x ^ 2 + y ^ 2) / r by ring]
  exact (div_eq_iff hz).mpr (by nlinarith)

theorem bogomolny_dyon_lower_bound (E B DPhi : ι → ℝ) :
    Real.sqrt (fieldDot E DPhi ^ 2 + fieldDot B DPhi ^ 2) ≤ ymhEnergyDensity E B DPhi := by
  obtain ⟨α, hα⟩ := sqrt_charge_attained (fieldDot E DPhi) (fieldDot B DPhi)
  rw [← hα]
  linarith [bogomolny_dyon_completion E B DPhi α,
    fieldNormSq_nonneg (fun k ↦ E k - Real.sin α * DPhi k),
    fieldNormSq_nonneg (fun k ↦ B k - Real.cos α * DPhi k)]

theorem bogomolny_dyon_saturation_iff (E B DPhi : ι → ℝ) :
    ymhEnergyDensity E B DPhi = Real.sqrt (fieldDot E DPhi ^ 2 + fieldDot B DPhi ^ 2) ↔
      ∃ α : ℝ, (∀ k, E k = Real.sin α * DPhi k) ∧ (∀ k, B k = Real.cos α * DPhi k) ∧
        0 ≤ Real.sin α * fieldDot E DPhi + Real.cos α * fieldDot B DPhi := by
  constructor
  · intro h
    obtain ⟨α, hα⟩ := sqrt_charge_attained (fieldDot E DPhi) (fieldDot B DPhi)
    have hE := fieldNormSq_nonneg (fun k ↦ E k - Real.sin α * DPhi k)
    have hB := fieldNormSq_nonneg (fun k ↦ B k - Real.cos α * DPhi k)
    have he := bogomolny_dyon_completion E B DPhi α
    have hEz : fieldNormSq (fun k ↦ E k - Real.sin α * DPhi k) = 0 := by linarith
    have hBz : fieldNormSq (fun k ↦ B k - Real.cos α * DPhi k) = 0 := by linarith
    refine ⟨α, ?_, ?_, hα ▸ Real.sqrt_nonneg _⟩
    · exact fun k ↦ sub_eq_zero.mp (congrFun ((fieldNormSq_eq_zero _).mp hEz) k)
    · exact fun k ↦ sub_eq_zero.mp (congrFun ((fieldNormSq_eq_zero _).mp hBz) k)
  · rintro ⟨α, hE, hB, hα⟩
    have he : fieldDot E DPhi = Real.sin α * fieldNormSq DPhi := by
      simp only [fieldNormSq, fieldDot, hE, Finset.mul_sum, mul_assoc]
    have hb : fieldDot B DPhi = Real.cos α * fieldNormSq DPhi := by
      simp only [fieldNormSq, fieldDot, hB, Finset.mul_sum, mul_assoc]
    have henergy := bogomolny_dyon_completion E B DPhi α
    simp only [hE, hB, sub_self, show fieldNormSq (fun _ : ι ↦ (0 : ℝ)) = 0 by
      simp [fieldNormSq, fieldDot], mul_zero, zero_add] at henergy
    have hdot : Real.sin α * fieldDot E DPhi + Real.cos α * fieldDot B DPhi =
        fieldNormSq DPhi := by
      rw [he, hb]
      nlinarith only [congrArg (fun x : ℝ ↦ x * fieldNormSq DPhi) (Real.sin_sq_add_cos_sq α)]
    have hsq : fieldDot E DPhi ^ 2 + fieldDot B DPhi ^ 2 = fieldNormSq DPhi ^ 2 := by
      rw [he, hb]
      nlinarith only [congrArg (fun x : ℝ ↦ x * fieldNormSq DPhi ^ 2)
        (Real.sin_sq_add_cos_sq α)]
    rw [henergy, hsq, Real.sqrt_sq (hdot ▸ hα)]
    exact hdot

theorem bogomolny_monopole_bound (B DPhi : ι → ℝ) :
    |fieldDot B DPhi| ≤ ymhEnergyDensity 0 B DPhi ∧
      (ymhEnergyDensity 0 B DPhi = |fieldDot B DPhi| ↔ B = DPhi ∨ B = -DPhi) := by
  have hq : |fieldDot B DPhi| =
      Real.sqrt (fieldDot (0 : ι → ℝ) DPhi ^ 2 + fieldDot B DPhi ^ 2) := by
    simp [fieldDot, Real.sqrt_sq_eq_abs]
  refine ⟨hq ▸ bogomolny_dyon_lower_bound 0 B DPhi, ?_⟩
  constructor
  · intro he
    by_cases h : 0 ≤ fieldDot B DPhi
    · have hh := bogomolny_dyon_completion 0 B DPhi 0
      simp [fieldNormSq, fieldDot] at hh
      rw [abs_of_nonneg h] at he
      have hz : fieldNormSq (B - DPhi) = 0 := by
        change (∑ k, (B k - DPhi k) * (B k - DPhi k)) = 0
        change ymhEnergyDensity 0 B DPhi = ∑ k, B k * DPhi k at he
        linarith
      exact Or.inl (sub_eq_zero.mp ((fieldNormSq_eq_zero _).mp hz))
    · have hh := bogomolny_dyon_completion 0 B DPhi Real.pi
      simp [fieldNormSq, fieldDot, sub_neg_eq_add] at hh
      rw [abs_of_neg (lt_of_not_ge h)] at he
      have hz : fieldNormSq (B + DPhi) = 0 := by
        change (∑ k, (B k + DPhi k) * (B k + DPhi k)) = 0
        change ymhEnergyDensity 0 B DPhi = -(∑ k, B k * DPhi k) at he
        linarith
      exact Or.inr (eq_neg_of_add_eq_zero_left ((fieldNormSq_eq_zero _).mp hz))
  · intro h
    rcases h with h | h <;> subst B
    · rw [show fieldDot DPhi DPhi = fieldNormSq DPhi from rfl,
        abs_of_nonneg (fieldNormSq_nonneg DPhi)]
      simpa [fieldNormSq, fieldDot] using bogomolny_dyon_completion 0 DPhi DPhi 0
    · have hneg : fieldDot (-DPhi) DPhi = -fieldNormSq DPhi := by
        simp [fieldDot, fieldNormSq, Finset.sum_neg_distrib]
      rw [hneg, abs_neg, abs_of_nonneg (fieldNormSq_nonneg DPhi)]
      simpa [fieldNormSq, fieldDot, Finset.sum_neg_distrib] using
        bogomolny_dyon_completion 0 (-DPhi) DPhi Real.pi

end Energy

section PrasadSommerfield

/-- The magnetic gauge profile in the dimensionless radius. -/
def psK (u : ℝ) : ℝ := u / Real.sinh u

/-- The Higgs profile in the dimensionless radius. -/
def psH (u : ℝ) : ℝ := u * Real.cosh u / Real.sinh u - 1

theorem ps_solves_bogomolny_ode (u : ℝ) (hu : 0 < u) :
    HasDerivAt psK (-(psK u * psH u) / u) u ∧
      HasDerivAt psH ((psH u - (psK u ^ 2 - 1)) / u) u := by
  have hs := (Real.sinh_pos_iff.mpr hu).ne'
  constructor
  · convert (hasDerivAt_id u).div (Real.hasDerivAt_sinh u) hs using 1 <;> try rfl
    dsimp [psK, psH]
    field_simp [hu.ne', hs]
    ring
  · convert (((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).div
      (Real.hasDerivAt_sinh u) hs).sub_const (1 : ℝ) using 1 <;> try rfl
    dsimp [psK, psH]
    field_simp [hu.ne', hs]
    rw [show Real.cosh u ^ 2 = Real.sinh u ^ 2 + 1 by
      linarith only [Real.cosh_sq_sub_sinh_sq u]]
    ring

/-- Spherical magnetic and Higgs gradient energy with the radial equations inserted. -/
def psEnergyDensity (u : ℝ) : ℝ :=
  (-(psK u * psH u) / u) ^ 2 + ((1 - psK u ^ 2) / u) ^ 2 / 2 +
    (((psH u - (psK u ^ 2 - 1)) - psH u) / u) ^ 2 / 2 +
    (psK u * psH u / u) ^ 2

/-- The boundary expression for the spherical energy. -/
def psBoundary (u : ℝ) : ℝ := psH u * (1 - psK u ^ 2) / u

theorem ps_radial_energy_exact_deriv (u : ℝ) (hu : 0 < u) :
    psEnergyDensity u =
      deriv psK u ^ 2 + ((1 - psK u ^ 2) / u) ^ 2 / 2 +
        ((u * deriv psH u - psH u) / u) ^ 2 / 2 + (psK u * psH u / u) ^ 2 := by
  obtain ⟨hK, hH⟩ := ps_solves_bogomolny_ode u hu
  rw [hK.deriv, hH.deriv, mul_div_cancel₀ _ hu.ne']
  rfl

theorem ps_total_deriv (u : ℝ) (hu : 0 < u) :
    HasDerivAt psBoundary (psEnergyDensity u) u := by
  obtain ⟨hK, hH⟩ := ps_solves_bogomolny_ode u hu
  have hd := (hH.mul ((hasDerivAt_const u (1 : ℝ)).sub (hK.pow 2))).div
    (hasDerivAt_id u) hu.ne'
  convert hd using 1 <;> try rfl
  dsimp [psEnergyDensity]
  field_simp [hu.ne']
  ring

private theorem psK_origin : Tendsto psK (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hratio : Tendsto (fun u : ℝ ↦ Real.sinh u / u) (𝓝[>] 0) (𝓝 1) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := Real.cosh) (g' := fun _ ↦ 1)
    · exact Eventually.of_forall Real.hasDerivAt_sinh
    · exact Eventually.of_forall hasDerivAt_id
    · exact Eventually.of_forall fun _ ↦ one_ne_zero
    · simpa [ContinuousWithinAt] using
        Real.continuous_sinh.continuousWithinAt (s := Ioi 0) (x := 0)
    · exact continuousWithinAt_id
    · simpa [ContinuousWithinAt] using
        Real.continuous_cosh.continuousWithinAt (s := Ioi 0) (x := 0)
  exact (by simpa only [inv_one] using hratio.inv₀ one_ne_zero :
    Tendsto (fun u : ℝ ↦ (Real.sinh u / u)⁻¹) (𝓝[>] 0) (𝓝 1)) |>.congr
    (fun u ↦ inv_div (Real.sinh u) u)

private theorem psH_div_origin :
    Tendsto (fun u : ℝ ↦ psH u / u) (𝓝[>] 0) (𝓝 0) := by
  have hratio : Tendsto (fun u : ℝ ↦ (u * Real.cosh u - Real.sinh u) / u ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := fun u ↦ u * Real.sinh u)
      (g' := fun u ↦ 2 * u)
    · apply Eventually.of_forall
      intro u
      convert (((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub
        (Real.hasDerivAt_sinh u)) using 1 <;> try rfl
      simp
    · apply Eventually.of_forall
      intro u
      have h := (hasDerivAt_id u).pow 2
      change HasDerivAt (fun x : ℝ ↦ x ^ 2) _ u at h
      simpa using h
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with u hu
      exact mul_ne_zero (by norm_num) (ne_of_gt (show 0 < u from hu))
    · have hc : Continuous (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) :=
        (continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh
      simpa [ContinuousWithinAt] using hc.continuousWithinAt (s := Ioi 0) (x := 0)
    · have hc : Continuous (fun u : ℝ ↦ u ^ 2) := continuous_id.pow 2
      simpa [ContinuousWithinAt, Pi.pow_apply] using hc.continuousWithinAt (s := Ioi 0) (x := 0)
    · have hlim : Tendsto (fun u : ℝ ↦ Real.sinh u / 2) (𝓝[>] 0) (𝓝 0) := by
        simpa [ContinuousWithinAt] using (Real.continuous_sinh.div_const (2 : ℝ)).continuousWithinAt
          (s := Ioi 0) (x := 0)
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with u hu
      field_simp [ne_of_gt (show 0 < u from hu)]
  have hlim := hratio.mul psK_origin
  rw [zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with u hu
  have hs := (Real.sinh_pos_iff.mpr hu).ne'
  dsimp [psK, psH]
  field_simp [ne_of_gt (show 0 < u from hu), hs]

private theorem ps_exp_neg_limit : Tendsto (fun u : ℝ ↦ Real.exp (-u)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

private theorem psK_infinity : Tendsto psK atTop (𝓝 0) := by
  have hnum : Tendsto (fun u : ℝ ↦ 2 * (u * Real.exp (-u))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (2 : ℝ)
  have hdenom : Tendsto (fun u : ℝ ↦ 1 - Real.exp (-u) ^ 2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (ps_exp_neg_limit.pow 2))
  have hlim := hnum.div hdenom one_ne_zero
  rw [zero_div] at hlim
  refine hlim.congr ?_
  intro u
  have he := (Real.exp_pos u).ne'
  simp only [psK, Real.sinh_eq, Real.exp_neg, Pi.div_apply]
  rw [div_div_eq_mul_div]
  have hd : Real.exp u - (Real.exp u)⁻¹ = Real.exp u * (1 - ((Real.exp u)⁻¹) ^ 2) := by
    field_simp [he]
  rw [hd, div_mul_eq_div_div]
  ring

private theorem psH_div_infinity : Tendsto (fun u : ℝ ↦ psH u / u) atTop (𝓝 1) := by
  have hnum : Tendsto (fun u : ℝ ↦ 1 + Real.exp (-u) ^ 2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add (ps_exp_neg_limit.pow 2))
  have hdenom : Tendsto (fun u : ℝ ↦ 1 - Real.exp (-u) ^ 2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (ps_exp_neg_limit.pow 2))
  have hinv : Tendsto (fun u : ℝ ↦ 1 / u) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ ↦ u⁻¹) atTop (𝓝 0))
  have hlim := (hnum.div hdenom one_ne_zero).sub hinv
  rw [div_one, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with u hu
  have he := (Real.exp_pos u).ne'
  dsimp
  rw [psH, sub_div, show u * Real.cosh u / Real.sinh u / u =
    Real.cosh u / Real.sinh u by
      rw [mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (ne_of_gt (show 0 < u from hu))]]
  congr 1
  simp only [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show Real.exp u + (Real.exp u)⁻¹ =
      Real.exp u * (1 + ((Real.exp u)⁻¹) ^ 2) by field_simp [he],
    show Real.exp u - (Real.exp u)⁻¹ =
      Real.exp u * (1 - ((Real.exp u)⁻¹) ^ 2) by field_simp [he],
    mul_div_mul_left _ _ he]

theorem ps_origin_and_infinity_limits :
    Tendsto psBoundary (𝓝[>] 0) (𝓝 0) ∧ Tendsto psBoundary atTop (𝓝 1) := by
  have h (u : ℝ) : psH u / u * (1 - psK u ^ 2) = psBoundary u := by
    simp only [psBoundary, div_eq_mul_inv]
    ring
  constructor
  · simpa using (psH_div_origin.mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (psK_origin.pow 2))).congr h
  · simpa using (psH_div_infinity.mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (psK_infinity.pow 2))).congr h

theorem ps_monopole_exact_mass (g v : ℝ) (hg : 0 < g) (hv : 0 < v) :
    IntegrableOn psEnergyDensity (Ioi 0) ∧ (∫ u in Ioi 0, psEnergyDensity u) = 1 ∧
      (4 * Real.pi * v / g) * (∫ u in Ioi 0, psEnergyDensity u) = 4 * Real.pi * v / g ∧
      0 < 4 * Real.pi * v / g := by
  have hzero : psBoundary 0 = 0 := by simp [psBoundary]
  have hc : ContinuousWithinAt psBoundary (Ici 0) 0 := by
    rw [← Set.Ioi_insert, continuousWithinAt_insert_self]
    simpa [ContinuousWithinAt, hzero] using ps_origin_and_infinity_limits.1
  have hd (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivAt psBoundary (psEnergyDensity u) u :=
    ps_total_deriv u hu
  have hp (u : ℝ) (_ : u ∈ Ioi 0) : 0 ≤ psEnergyDensity u := by
    unfold psEnergyDensity
    positivity
  have hi := integrableOn_Ioi_deriv_of_nonneg hc hd hp ps_origin_and_infinity_limits.2
  have hm := integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi ps_origin_and_infinity_limits.2
  rw [hzero, sub_zero] at hm
  exact ⟨hi, hm, by rw [hm, mul_one], by positivity⟩

end PrasadSommerfield

section Charge

open Matrix
open scoped Matrix

def dszPairing (q₁ g₁ q₂ g₂ : ℝ) : ℝ := q₁ * g₂ - q₂ * g₁

def emAngularMomentum (q₁ g₁ q₂ g₂ : ℝ) : ℝ := dszPairing q₁ g₁ q₂ g₂ / (4 * Real.pi)

theorem dsz_half_integer_angMom_iff (q₁ g₁ q₂ g₂ : ℝ) :
    (∃ n : ℤ, dszPairing q₁ g₁ q₂ g₂ = 2 * Real.pi * n) ↔
      (∃ n : ℤ, emAngularMomentum q₁ g₁ q₂ g₂ = (n : ℝ) / 2) := by
  have hπ : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, (div_eq_iff hπ).mpr (by rw [h]; ring)⟩
  · rintro ⟨n, h⟩
    have hn := (div_eq_iff hπ).mp h
    exact ⟨n, by rw [hn]; ring⟩

theorem dirac_charge_quantization (q g : ℝ) (hg : g ≠ 0)
    (h : ∃ n : ℤ, dszPairing q 0 0 g = 2 * Real.pi * n) :
    q ∈ Set.range (fun n : ℤ ↦ (2 * Real.pi / g) * n) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  change (2 * Real.pi / g) * (n : ℝ) = q
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hg).mpr
  simpa [dszPairing] using hn.symm

abbrev ChargePair := ℤ × ℤ

abbrev ModularMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- Charge transport in the convention with central charge `nE + nM * τ`. -/
def sl2zCharge (M : ModularMatrix) (n : ChargePair) : ChargePair :=
  (M 0 0 * n.1 - M 0 1 * n.2, M 1 1 * n.2 - M 1 0 * n.1)

def sl2zDenom (M : ModularMatrix) (τ : ℂ) : ℂ := (M 1 0 : ℂ) * τ + (M 1 1 : ℂ)

def sl2zAct (M : ModularMatrix) (τ : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) / sl2zDenom M τ

def bpsDyonMass (v : ℝ) (τ : ℂ) (nE nM : ℤ) : ℝ :=
  v * ‖(nE : ℂ) + (nM : ℂ) * τ‖ / Real.sqrt τ.im

def dszLatticePairing (n m : ChargePair) : ℤ := n.1 * m.2 - m.1 * n.2

theorem sl2z_charge_action (M N : ModularMatrix) (n : ChargePair) :
    sl2zCharge 1 n = n ∧ sl2zCharge (M * N) n = sl2zCharge M (sl2zCharge N n) := by
  constructor
  · simp [sl2zCharge]
  · apply Prod.ext <;> simp only [sl2zCharge, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem dsz_pairing_sl2z_invariant (M : ModularMatrix) (hM : M.det = 1) (n m : ChargePair) :
    dszLatticePairing (sl2zCharge M n) (sl2zCharge M m) = dszLatticePairing n m := by
  rw [Matrix.det_fin_two] at hM
  unfold dszLatticePairing sl2zCharge
  dsimp
  linear_combination (n.1 * m.2 - m.1 * n.2) * hM

private theorem sl2zAct_eq_smul (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    sl2zAct (A : ModularMatrix) τ = ↑(A • τ : UpperHalfPlane) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [sl2zAct, sl2zDenom]

private theorem sl2zDenom_eq_denom (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) :
    UpperHalfPlane.denom (A : Matrix.GeneralLinearGroup (Fin 2) ℝ) τ =
      sl2zDenom (A : ModularMatrix) τ := by
  change (((A : ModularMatrix) 1 0 : ℝ) : ℂ) * τ + (((A : ModularMatrix) 1 1 : ℝ) : ℂ) = _
  simp only [Complex.ofReal_intCast, sl2zDenom]

private theorem sl2zDenom_ne_zero (M : ModularMatrix) (hM : M.det = 1) (τ : ℂ) (hτ : 0 < τ.im) :
    sl2zDenom M τ ≠ 0 := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨M, hM⟩
  let z : UpperHalfPlane := ⟨τ, hτ⟩
  have hd := UpperHalfPlane.denom_ne_zero
    (A : Matrix.GeneralLinearGroup (Fin 2) ℝ) z
  rw [sl2zDenom_eq_denom] at hd
  exact hd

theorem sl2z_preserves_upper_half_plane (M : ModularMatrix) (hM : M.det = 1)
    (τ : ℂ) (hτ : 0 < τ.im) :
    0 < (sl2zAct M τ).im ∧ (sl2zAct M τ).im = τ.im / ‖sl2zDenom M τ‖ ^ 2 := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨M, hM⟩
  let z : UpperHalfPlane := ⟨τ, hτ⟩
  have h : sl2zAct M τ = ((A • z : UpperHalfPlane) : ℂ) := sl2zAct_eq_smul A z
  rw [h]
  refine ⟨(A • z).im_pos, ?_⟩
  have him := ModularGroup.im_smul_eq_div_normSq A z
  rw [Complex.normSq_eq_norm_sq, sl2zDenom_eq_denom] at him
  exact him

theorem bpsDyonMass_sl2z_invariant (M : ModularMatrix) (hM : M.det = 1)
    (v : ℝ) (τ : ℂ) (hτ : 0 < τ.im) (n : ChargePair) :
    bpsDyonMass v (sl2zAct M τ) (sl2zCharge M n).1 (sl2zCharge M n).2 =
      bpsDyonMass v τ n.1 n.2 := by
  have hd := sl2zDenom_ne_zero M hM τ hτ
  have hn : ((sl2zCharge M n).1 : ℂ) + ((sl2zCharge M n).2 : ℂ) * sl2zAct M τ =
      ((n.1 : ℂ) + (n.2 : ℂ) * τ) / sl2zDenom M τ := by
    have hDet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = 1 := by
      exact_mod_cast (Matrix.det_fin_two M ▸ hM)
    unfold sl2zCharge sl2zAct
    push_cast
    apply (eq_div_iff hd).mpr
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    dsimp [sl2zDenom]
    linear_combination ((n.1 : ℂ) + (n.2 : ℂ) * τ) * hDet
  have hpos : 0 < ‖sl2zDenom M τ‖ := norm_pos_iff.mpr hd
  have hr := (sl2z_preserves_upper_half_plane M hM τ hτ).2
  unfold bpsDyonMass
  rw [hn, norm_div, hr, Real.sqrt_div hτ.le, Real.sqrt_sq hpos.le]
  field_simp [hpos.ne', (Real.sqrt_pos.2 hτ).ne']

theorem bpsDyonMass_S_duality (v : ℝ) (τ : ℂ) (hτ : 0 < τ.im) (nE nM : ℤ) :
    bpsDyonMass v (-1 / τ) nM (-nE) = bpsDyonMass v τ nE nM := by
  have h := bpsDyonMass_sl2z_invariant (ModularGroup.S : ModularMatrix) ModularGroup.S.prop
    v τ hτ (nE, nM)
  simpa [ModularGroup.S, sl2zAct, sl2zCharge, sl2zDenom] using h

theorem bpsDyonMass_T_duality (v : ℝ) (τ : ℂ) (hτ : 0 < τ.im) (nE nM : ℤ) :
    bpsDyonMass v (τ + 1) (nE - nM) nM = bpsDyonMass v τ nE nM := by
  have h := bpsDyonMass_sl2z_invariant (ModularGroup.T : ModularMatrix) ModularGroup.T.prop
    v τ hτ (nE, nM)
  simpa [ModularGroup.T, sl2zAct, sl2zCharge, sl2zDenom] using h

/-- The complex coupling at zero theta angle. -/
def imaginaryCoupling (g : ℝ) : ℂ := ((4 * Real.pi / g ^ 2 : ℝ) : ℂ) * Complex.I

theorem sl2z_weak_strong_coupling (g : ℝ) (hg : 0 < g) :
    0 < (imaginaryCoupling g).im ∧
      sl2zAct (ModularGroup.S : ModularMatrix) (imaginaryCoupling g) =
        imaginaryCoupling (4 * Real.pi / g) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  constructor
  · unfold imaginaryCoupling
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero]
    positivity
  · simp [ModularGroup.S, sl2zAct, sl2zDenom, imaginaryCoupling]
    field_simp [hπ, hgc, Complex.I_ne_zero]
    rw [Complex.I_sq]

end Charge

end D5.S3.Quantum.Gauge.BPSMonopoleDiracQuant4D
