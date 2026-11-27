/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullMemoryBMS4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bondi balance, angular memory spectrum, and the infrared memory obstruction. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The mass balance is conditional on the Bondi mass-loss equation. The angular memory
operator is formulated spectrally, and the infrared estimates use a scalar frequency profile. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace NullConeGravity

/-- The squared news averaged against the round angular measure. -/
def bondiFlux (N : Sphere4D → ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ n, ‖N n‖ ^ 2 ∂sphereMeasure

theorem bondiFlux_nonneg (N : Sphere4D → ℂ) : 0 ≤ bondiFlux N :=
  mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)

private instance : CompactSpace Sphere4D :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E3) 1)

private instance : sphereMeasure.IsOpenPosMeasure :=
  inferInstanceAs ((volume : Measure E3).toSphere.IsOpenPosMeasure)

theorem bondiFlux_eq_zero_iff (N : Sphere4D → ℂ) (hN : Continuous N) :
    bondiFlux N = 0 ↔ N = 0 := by
  constructor
  · intro hflux
    ext n
    by_contra hnonzero
    have hnonzero' : N n ≠ 0 := hnonzero
    have hcont : Continuous (fun n => ‖N n‖ ^ 2) := hN.norm.pow 2
    have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := sphereMeasure)
      hcont (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun n => sq_nonneg ‖N n‖) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnonzero'))
    exact (mul_pos (by positivity : 0 < (4 * Real.pi)⁻¹) hpos).ne' hflux
  · rintro rfl
    simp [bondiFlux]

private theorem continuous_bondiFlux {N : ℝ → Sphere4D → ℂ}
    (hN : Continuous (Function.uncurry N)) :
    Continuous (fun u => bondiFlux (N u)) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (n : Sphere4D) => ‖N u n‖ ^ 2) :=
    hN.norm.pow 2
  have hint := continuous_parametric_integral_of_continuous (μ := sphereMeasure)
    hcont isCompact_univ
  simp only [setIntegral_univ] at hint
  exact continuous_const.mul hint

/-- The Bondi mass is antitone whenever it obeys the mass-loss equation. -/
theorem bondi_mass_loss_nonpos {M : ℝ → ℝ} {N : ℝ → Sphere4D → ℂ}
    (hlaw : ∀ u, HasDerivAt M (-bondiFlux (N u)) u) : Antitone M := by
  refine antitone_of_deriv_nonpos (fun u => (hlaw u).differentiableAt) (fun u => ?_)
  rw [(hlaw u).deriv]
  exact neg_nonpos.mpr (bondiFlux_nonneg (N u))

theorem bondi_energy_radiated_nonneg (N : ℝ → Sphere4D → ℂ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ u in a..b, bondiFlux (N u) :=
  intervalIntegral.integral_nonneg_of_forall hab (fun u => bondiFlux_nonneg (N u))

/-- The exact difference of Bondi masses equals the integrated outgoing flux. -/
theorem bondi_energy_balance {M : ℝ → ℝ} {N : ℝ → Sphere4D → ℂ}
    (hM : Continuous (deriv M))
    (hlaw : ∀ u, HasDerivAt M (-bondiFlux (N u)) u) (a b : ℝ) :
    M a - M b = ∫ u in a..b, bondiFlux (N u) := by
  have hderiv : deriv M = fun u => -bondiFlux (N u) :=
    funext fun u => (hlaw u).deriv
  rw [hderiv] at hM
  have hint := hM.intervalIntegrable (μ := volume) a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hlaw u) hint
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem bondi_strict_mass_loss_of_nonzero_news {M : ℝ → ℝ} {N : ℝ → Sphere4D → ℂ}
    (hN : Continuous (Function.uncurry N))
    (hlaw : ∀ u, HasDerivAt M (-bondiFlux (N u)) u) {a b u₀ : ℝ}
    (hu₀ : u₀ ∈ Ioo a b) (hnews : N u₀ ≠ 0) : M b < M a := by
  have hslice : Continuous (N u₀) := hN.comp (continuous_const.prodMk continuous_id)
  have hflux : 0 < bondiFlux (N u₀) :=
    lt_of_le_of_ne (bondiFlux_nonneg _) (Ne.symm ((bondiFlux_eq_zero_iff _ hslice).not.mpr hnews))
  have hint := intervalIntegral.integral_pos (hu₀.1.trans hu₀.2)
    (continuous_bondiFlux hN).continuousOn (fun u _ => bondiFlux_nonneg (N u))
    ⟨u₀, ⟨hu₀.1.le, hu₀.2.le⟩, hflux⟩
  have hderiv : deriv M = fun u => -bondiFlux (N u) :=
    funext fun u => (hlaw u).deriv
  have hM : Continuous (deriv M) := hderiv ▸ (continuous_bondiFlux hN).neg
  rw [← bondi_energy_balance hM hlaw a b] at hint
  exact sub_pos.mp hint

/-- The degree eigenvalue of the round angular memory operator. -/
def memoryEllipticEigenvalue (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + 1) * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + 2)

theorem memoryElliptic_zero_iff (ℓ : ℕ) :
    memoryEllipticEigenvalue ℓ = 0 ↔ ℓ = 0 ∨ ℓ = 1 := by
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have h₁ : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (ℓ : ℝ) + 2 ≠ 0 := by positivity
  have hsub : (ℓ : ℝ) - 1 = 0 ↔ ℓ = 1 := by
    rw [sub_eq_zero]
    exact_mod_cast (Iff.rfl : ℓ = 1 ↔ ℓ = 1)
  simp [memoryEllipticEigenvalue, mul_eq_zero, h₁, h₂, hsub]

theorem memoryElliptic_pos_iff (ℓ : ℕ) : 0 < memoryEllipticEigenvalue ℓ ↔ 2 ≤ ℓ := by
  constructor
  · intro h
    by_contra hsmall
    have hz : ℓ = 0 ∨ ℓ = 1 := by omega
    exact h.ne' ((memoryElliptic_zero_iff ℓ).mpr hz)
  · intro h
    have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast h
    have hsub : 0 < (ℓ : ℝ) - 1 := by linarith
    unfold memoryEllipticEigenvalue
    positivity

/-- Total multiplicity of the two degrees annihilated by the memory operator. -/
theorem poincare_translation_dim_eq_four : harmonicMult 4 0 + harmonicMult 4 1 = 4 := by
  norm_num [harmonicMult_four]

/-- The squared inverse eigenvalues with their multiplicities, starting at degree two. -/
theorem memoryGreenSq_summable :
    Summable (fun k : ℕ => (harmonicMult 4 (k + 2) : ℝ) /
      memoryEllipticEigenvalue (k + 2) ^ 2) := by
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ (7 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ (7 : ℕ)) 2).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (7 : ℕ)))
  refine (hsum.mul_left 12).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  let x : ℝ := (k : ℝ) + 2
  have hx : 2 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hxpos : 0 < x := by linarith
  have hfactor : 0 ≤ x - 1 := by linarith
  have hLower : x ^ 4 / 2 ≤ x * (x + 1) * (x - 1) * (x + 2) := by
    calc
      x ^ 4 / 2 = x * x * (x / 2) * x := by ring
      _ ≤ _ := by gcongr <;> linarith
  have hden : (x ^ 4 / 2) ^ 2 ≤ (x * (x + 1) * (x - 1) * (x + 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hLower 2
  simp only [harmonicMult_four, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    memoryEllipticEigenvalue]
  change (2 * x + 1) / (x * (x + 1) * (x - 1) * (x + 2)) ^ 2 ≤ 12 * (1 / x ^ 7)
  calc
    _ ≤ (3 * x) / ((x ^ 4 / 2) ^ 2) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    _ = _ := by field_simp; ring

/-- Frequency density for the radiative one-particle norm. -/
def irDensity (f : ℝ → ℂ) (ω : ℝ) : ℝ := ‖f ω‖ ^ 2 / ω

private theorem irDensity_nonneg (f : ℝ → ℂ) {ω : ℝ} (hω : 0 ≤ ω) :
    0 ≤ irDensity f ω :=
  div_nonneg (sq_nonneg _) hω

private theorem continuousOn_irDensity {f : ℝ → ℂ} {s : Set ℝ}
    (hf : ContinuousOn f s) (hs : ∀ x ∈ s, 0 < x) : ContinuousOn (irDensity f) s :=
  (hf.norm.pow 2).div continuousOn_id (fun x hx => (hs x hx).ne')

private theorem irDensity_intervalIntegrable {f : ℝ → ℂ} (hf : Continuous f)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (irDensity f) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact continuousOn_irDensity hf.continuousOn (fun _ hx => ha.trans_le hx.1)

/-- Nonzero memory gives a logarithmic lower bound, divergence to positive infinity, and
failure of integrability at the infrared endpoint. -/
theorem nonzero_memory_ir_diverges {f : ℝ → ℂ} (hf : Continuous f) (hmem : f 0 ≠ 0)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (∃ a > 0, ∃ δ ∈ Ioc (0 : ℝ) Λ, ∀ ε ∈ Ioo (0 : ℝ) δ,
      a * Real.log (δ / ε) ≤ ∫ ω in ε..Λ, irDensity f ω) ∧
    Tendsto (fun ε => ∫ ω in ε..Λ, irDensity f ω) (𝓝[>] 0) atTop ∧
      ¬ IntegrableOn (irDensity f) (Ioo (0 : ℝ) Λ) := by
  let a := ‖f 0‖ ^ 2 / 2
  have hnorm : 0 < ‖f 0‖ := norm_pos_iff.mpr hmem
  have ha : 0 < a := by dsimp [a]; positivity
  have hlt : a < ‖f 0‖ ^ 2 := by dsimp [a]; linarith [sq_pos_of_pos hnorm]
  have hnear : ∀ᶠ ω in 𝓝 (0 : ℝ), a < ‖f ω‖ ^ 2 :=
    (hf.norm.pow 2).continuousAt.eventually (lt_mem_nhds hlt)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let δ := min (r / 2) Λ
  have hδ : 0 < δ := lt_min (by positivity) hΛ
  have hδΛ : δ ≤ Λ := min_le_right _ _
  have hinv (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) δ) :
      a * Real.log (δ / ε) ≤ ∫ ω in ε..Λ, irDensity f ω := by
    have hi := irDensity_intervalIntegrable hf hε.1 (hε.2.le.trans hδΛ)
    have his := irDensity_intervalIntegrable hf hε.1 hε.2.le
    have hcont : ContinuousOn (fun ω : ℝ => a * ω⁻¹) [[ε, δ]] := by
      rw [uIcc_of_le hε.2.le]
      exact continuousOn_const.mul (continuousOn_id.inv₀ (fun _ hω => (hε.1.trans_le hω.1).ne'))
    calc
      a * Real.log (δ / ε) = ∫ ω in ε..δ, a * ω⁻¹ := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hε.1 hδ]
      _ ≤ ∫ ω in ε..δ, irDensity f ω := by
        refine intervalIntegral.integral_mono_on hε.2.le hcont.intervalIntegrable his ?_
        intro ω hω
        have hωpos := hε.1.trans_le hω.1
        have hrbound : ω < r := hω.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
        have hmem' : ω ∈ Metric.ball (0 : ℝ) r := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hωpos] using hrbound
        simpa only [irDensity, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hball ω hmem').le (inv_nonneg.mpr hωpos.le)
      _ ≤ ∫ ω in ε..Λ, irDensity f ω :=
        intervalIntegral.integral_mono_interval le_rfl hε.2.le hδΛ
          ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun _ hω => irDensity_nonneg f (hε.1.trans hω.1).le)) hi
  have ht : Tendsto (fun ε : ℝ => ∫ ω in ε..Λ, irDensity f ω) (𝓝[>] 0) atTop := by
    have hratio : Tendsto (fun ε : ℝ => δ / ε) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hδ
    refine tendsto_atTop_mono' _ ?_ ((Real.tendsto_log_atTop.comp hratio).const_mul_atTop ha)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε using hinv ε hε
  refine ⟨⟨a, ha, δ, ⟨hδ, hδΛ⟩, hinv⟩, ht, ?_⟩
  intro hint
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) Λ)] irDensity f :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun _ hω => irDensity_nonneg f hω.1.le)
  let B := ∫ ω in Ioo (0 : ℝ) Λ, irDensity f ω
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ ω in ε..Λ, irDensity f ω ≤ B := by
    filter_upwards [Ioo_mem_nhdsGT hΛ] with ε hε
    rw [intervalIntegral.integral_of_le hε.2.le, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_set hint hnonneg
      (Ioo_subset_Ioo_left hε.1.le).eventuallySubset
  have hlarge := (tendsto_atTop.1 ht) (B + 1)
  obtain ⟨ε, hεle, hεge⟩ := (hevent.and hlarge).exists
  linarith

/-- A positive Hölder rate of vanishing makes the infrared norm integrable. -/
theorem zero_memory_ir_integrable {f : ℝ → ℂ} {Λ C α : ℝ} (hΛ : 0 < Λ) (hα : 0 < α)
    (hf : ContinuousOn f (Icc 0 Λ))
    (hbound : ∀ ω ∈ Ioo (0 : ℝ) Λ, ‖f ω‖ ≤ C * ω ^ α) :
    IntegrableOn (irDensity f) (Ioo (0 : ℝ) Λ) := by
  have hpow : IntegrableOn (fun ω : ℝ => ω ^ (2 * α - 1)) (Ioo (0 : ℝ) Λ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hΛ).2 (by linarith)
  have hmajor : IntegrableOn (fun ω : ℝ => C ^ 2 * ω ^ (2 * α - 1)) (Ioo (0 : ℝ) Λ) :=
    hpow.const_mul _
  refine hmajor.mono' ((continuousOn_irDensity (hf.mono Ioo_subset_Icc_self)
    (fun _ hω => hω.1)).aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun ω hω => ?_)
  rw [Real.norm_of_nonneg (irDensity_nonneg f hω.1.le), irDensity]
  calc
    ‖f ω‖ ^ 2 / ω ≤ (C * ω ^ α) ^ 2 / ω := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbound ω hω) 2) hω.1.le
    _ = _ := by
      have hpow₂ : ω ^ (2 * α) = (ω ^ α) ^ (2 : ℕ) := by
        rw [mul_comm]
        exact Real.rpow_mul_natCast hω.1.le α 2
      rw [mul_pow, Real.rpow_sub hω.1, Real.rpow_one, hpow₂]
      ring

/-- An inverse-frequency integral over each dyadic bin has the same weight. -/
theorem dyadic_memory_bin_weight (k : ℕ) :
    (∫ ω in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, ω⁻¹) = Real.log 2 := by
  rw [integral_inv_of_pos (by positivity) (by positivity)]
  congr 1
  rw [pow_succ]
  field_simp

/-- A real memory amplitude in each normalized dyadic infrared mode. -/
def dyadicMemoryProfile (m : ℝ) (_ : ℕ) : ℂ :=
  ((m * Real.sqrt (Real.log 2) : ℝ) : ℂ)

theorem dyadic_memory_not_summable_sq {m : ℝ} (hm : m ≠ 0) :
    ¬ Summable (fun k : ℕ => ‖dyadicMemoryProfile m k‖ ^ 2) := by
  have hsqrt : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have hconst : ‖((m * Real.sqrt (Real.log 2) : ℝ) : ℂ)‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by exact_mod_cast mul_ne_zero hm hsqrt.ne'))
  intro hs
  exact hconst (tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero)

theorem dyadic_memory_diff_summable_sq_iff (m₁ m₂ : ℝ) :
    Summable (fun k : ℕ => ‖dyadicMemoryProfile m₁ k - dyadicMemoryProfile m₂ k‖ ^ 2) ↔
      m₁ = m₂ := by
  have hdiff (k : ℕ) : dyadicMemoryProfile m₁ k - dyadicMemoryProfile m₂ k =
      dyadicMemoryProfile (m₁ - m₂) k := by
    simp only [dyadicMemoryProfile, sub_mul, Complex.ofReal_sub]
  simp only [hdiff]
  constructor
  · intro hs
    by_contra h
    exact dyadic_memory_not_summable_sq (sub_ne_zero.mpr h) hs
  · rintro rfl
    simp [dyadicMemoryProfile]

end NullConeGravity
