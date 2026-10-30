/- GID: D5/S3/Combinatorics/Partitions/EtaOddOccupation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/EtaOddOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.Discriminant]
   utility: none
   digest: Eta normalization and even-rank S transformation of independent odd-occupation coefficients. -/

import D5.S3.Combinatorics.Partitions.AnalyticOddOccupation
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Exact eta normalization of the independent odd-occupation series. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators
open Complex

namespace D5.S3.Combinatorics.Partitions.EtaOddOccupation

open D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation

/-- The independently counted coefficients, evaluated in the ordinary complex topology. -/
def oddCoefficientSeries (r : ℕ) (q : ℂ) : ℂ :=
  ∑' N : ℕ, (Nat.card (ColouredOddFiber (Fin r) N) : ℂ) * q ^ N

private theorem half_q_norm_lt_one (τ : ℂ) (hτ : 0 < τ.im) :
    ‖exp (Real.pi * I * τ)‖ < 1 := by
  rw [norm_exp, Real.exp_lt_one_iff]
  simpa [mul_re, mul_im] using neg_lt_zero.mpr (mul_pos Real.pi_pos hτ)

private theorem multipliable_odd {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (2 * n + 1)) := by
  apply multipliable_one_add_of_summable (f := fun n : ℕ => -q ^ (2 * n + 1))
  have hs := (summable_norm_geometric_of_norm_lt_one hq).comp_injective
    (i := fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp only at h; omega)
  simpa only [Function.comp_def, norm_neg] using hs

private theorem euler_even_odd {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
      (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) =
        ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by decide)
  have he := ModularForm.multipliable_one_sub_pow hq2
  have ho := multipliable_odd hq
  have hpow (n : ℕ) : (q ^ 2) ^ (n + 1) = q ^ (2 * n + 1 + 1) := by
    rw [← pow_mul]
    congr 1
  have he' : Multipliable (fun n : ℕ => 1 - q ^ (2 * n + 1 + 1)) :=
    he.congr (fun n => by rw [hpow])
  simpa only [hpow] using
    tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) ho he'

private theorem odd_product_mul_series (r : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ r * oddCoefficientSeries r q = 1 := by
  have hp := ((multipliable_odd hq).hasProd.pow r).mul
    (hasProd_odd_character (Fin r) hq)
  have hn (n : ℕ) : 1 - q ^ (2 * n + 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hb : ‖q ^ (2 * n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
    rw [← h, norm_one] at hb
    exact lt_irrefl _ hb
  have he : (fun n : ℕ => (1 - q ^ (2 * n + 1)) ^ r *
      ((1 - q ^ (2 * n + 1))⁻¹) ^ Fintype.card (Fin r)) = fun _ => (1 : ℂ) := by
    funext n
    simp only [Fintype.card_fin, ← mul_pow, mul_inv_cancel₀ (hn n), one_pow]
  rw [he] at hp
  exact hp.unique hasProd_one

private theorem eta_ratio_mul_odd (τ : ℂ) (hτ : 0 < τ.im) :
    (ModularForm.eta τ / ModularForm.eta (τ / 2)) *
      (∏' n : ℕ, (1 - exp (Real.pi * I * τ) ^ (2 * n + 1))) =
        exp (2 * Real.pi * I * τ / 48) := by
  have hhalf : 0 < (τ / 2).im := by simpa using half_pos hτ
  have hne := ModularForm.eta_ne_zero hhalf
  have hsplit := euler_even_odd (half_q_norm_lt_one τ hτ)
  have hqfull : exp (Real.pi * I * τ) ^ 2 = exp (2 * Real.pi * I * τ) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have hqhalf : Function.Periodic.qParam 1 (τ / 2) = exp (Real.pi * I * τ) := by
    simp only [Function.Periodic.qParam, ofReal_one, div_one]
    congr 1
    ring
  have hexp : exp (2 * Real.pi * I * τ / 48) *
      Function.Periodic.qParam 24 (τ / 2) = Function.Periodic.qParam 24 τ := by
    simp only [Function.Periodic.qParam, ofReal_ofNat]
    rw [← exp_add]
    congr 1
    ring
  rw [div_mul_eq_mul_div, div_eq_iff hne]
  rw [ModularForm.eta, ModularForm.eta]
  simp only [ModularForm.eta_q, hqhalf]
  have hfull : Function.Periodic.qParam 1 τ = exp (2 * Real.pi * I * τ) := by
    simp [Function.Periodic.qParam]
  rw [hfull]
  rw [hqfull] at hsplit
  calc
    _ = Function.Periodic.qParam 24 τ *
        ((∏' n : ℕ, (1 - exp (Real.pi * I * τ) ^ (2 * n + 1))) *
          (∏' n : ℕ, (1 - exp (2 * Real.pi * I * τ) ^ (n + 1)))) := by ring
    _ = _ := by rw [hsplit, ← hexp]; ring

/-- All ranks and arbitrary complex scalar insertions, including zero, have the
exact eta normalization. The coefficients are defined by finite occupation fibres. -/
theorem normalized_odd_character_eq_eta (r : ℕ) (c τ : ℂ) (hτ : 0 < τ.im) :
    c * exp (2 * Real.pi * I * τ * r / 48) *
      oddCoefficientSeries r (exp (Real.pi * I * τ)) =
        c * (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ r := by
  have hp := odd_product_mul_series r (half_q_norm_lt_one τ hτ)
  have he := congrArg (fun z : ℂ => z ^ r) (eta_ratio_mul_odd τ hτ)
  rw [mul_pow, ← exp_nat_mul] at he
  have hex : (r : ℂ) * (2 * Real.pi * I * τ / 48) =
      2 * Real.pi * I * τ * r / 48 := by ring
  rw [hex] at he
  calc
    _ = c * (((ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ r *
        (∏' n : ℕ, (1 - exp (Real.pi * I * τ) ^ (2 * n + 1))) ^ r) *
          oddCoefficientSeries r (exp (Real.pi * I * τ))) := by rw [he]; ring
    _ = _ := by rw [mul_assoc, hp, mul_one]

private theorem eta_ratio_S_square (τ : ℂ) (hτ : 0 < τ.im) :
    (ModularForm.eta (-1 / τ) / ModularForm.eta ((-1 / τ) / 2)) ^ 2 =
      (2 : ℂ)⁻¹ * (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ 2 := by
  have htwo : 0 < (2 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hτ
  have ht : τ ≠ 0 := by intro h; simp [h] at hτ
  have h1 := ModularForm.eta_comp_eq_csqrt_I_inv hτ
  have h2 := ModularForm.eta_comp_eq_csqrt_I_inv htwo
  change ModularForm.eta (-1 / τ) = (sqrt I)⁻¹ * (sqrt τ * ModularForm.eta τ) at h1
  change ModularForm.eta (-1 / (2 * τ)) =
    (sqrt I)⁻¹ * (sqrt (2 * τ) * ModularForm.eta (2 * τ)) at h2
  have harg : (-1 / τ) / 2 = -1 / (2 * τ) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs (z : ℂ) : sqrt z ^ 2 = z := cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)
  rw [harg, h1, h2, div_pow]
  simp only [mul_pow, inv_pow, hs]
  field_simp [ht, I_ne_zero, ModularForm.eta_ne_zero htwo]

/-- The even-rank S transform has the exact factor 2^(-m). No multiplicative
identity for principal square roots is required. -/
theorem normalized_odd_character_S (m : ℕ) (c τ : ℂ) (hτ : 0 < τ.im) :
    c * exp (2 * Real.pi * I * (-1 / τ) * (2 * m) / 48) *
      oddCoefficientSeries (2 * m) (exp (Real.pi * I * (-1 / τ))) =
        c * ((2 : ℂ) ^ m)⁻¹ *
          (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ (2 * m) := by
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  calc
    _ = c * (ModularForm.eta (-1 / τ) /
        ModularForm.eta ((-1 / τ) / 2)) ^ (2 * m) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        normalized_odd_character_eq_eta (2 * m) c (-1 / τ) hS
    _ = _ := by
      rw [pow_mul, eta_ratio_S_square τ hτ, mul_pow, inv_pow, ← pow_mul]
      ring

end D5.S3.Combinatorics.Partitions.EtaOddOccupation

#print axioms D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_eq_eta
#print axioms D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_S
