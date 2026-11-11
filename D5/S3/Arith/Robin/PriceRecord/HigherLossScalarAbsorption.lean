/- GID: D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Exact budget algebra and two Young inequalities retain the sharp error rate. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Scalar reduction of the finite budget and absorption of its error terms. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HigherLossScalarAbsorption
open Real Filter
open scoped Topology

def a : ℝ := 12000
def d : ℝ := 24000
def q : ℝ := 2 * a ^ 2 + d
def finalConstant : ℝ := 52 * q + d + 4

theorem scalar_budget_reduction {X T V W Δ δ R : ℝ}
    (hX : exp 2 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hVT : V ≤ T) (hWΔ : W ≤ Δ + δ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 2 * log X) (hhalf : log X / 2 ≤ log (X / 2))
    (hR : R ≤ 6 * V * W / (X ^ 2 * log (X / 2)) + δ / (X * log X))
    (hΔ : Δ ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R +
      X * log X * R + log X ^ 2)) :
    R ≤ a * T / X ^ (5 / 4 : ℝ) * sqrt R + a * (T / X) * R +
      d * T * log X / X ^ 2 + 2 / X := by
  have hX0 : 0 < X := (exp_pos 2).trans_le hX
  have hL : 2 ≤ log X := (le_log_iff_exp_le hX0).mpr hX
  have hL0 : 0 < log X := by linarith
  have hhalf0 : 0 < log (X / 2) := by linarith
  have hδsq : δ ≤ log X ^ 2 := by
    nlinarith only [hδ, mul_nonneg hL0.le (sub_nonneg.mpr hL)]
  have hslack : δ / (X * log X) ≤ 2 / X := by
    apply (div_le_div_iff₀ (mul_pos hX0 hL0) hX0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hδ hX0.le]
  have hprod : V * W ≤ T * (Δ + δ) :=
    mul_le_mul hVT hWΔ hW hT
  have hnum : 0 ≤ 6 * T * (Δ + δ) := by
    have := hW.trans hWΔ
    positivity
  have hmain : 6 * V * W / (X ^ 2 * log (X / 2)) ≤
      12 * T * (Δ + δ) / (X ^ 2 * log X) := by
    calc
      _ ≤ 6 * T * (Δ + δ) / (X ^ 2 * log (X / 2)) :=
        div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ 6 * T * (Δ + δ) / (X ^ 2 * (log X / 2)) :=
        div_le_div_of_nonneg_left hnum (by positivity)
          (mul_le_mul_of_nonneg_left hhalf (sq_nonneg X))
      _ = _ := by ring
  have hΔδ : Δ + δ ≤ 1000 * X ^ (3 / 4 : ℝ) * log X * sqrt R +
      1000 * X * log X * R + 1001 * log X ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hΔδ
    (show 0 ≤ 12 * T / (X ^ 2 * log X) by positivity)
  have hpow : X ^ (3 / 4 : ℝ) * X ^ (5 / 4 : ℝ) = X ^ 2 := by
    rw [← rpow_add hX0]
    norm_num
  have halg : (12 * T / (X ^ 2 * log X)) *
      (1000 * X ^ (3 / 4 : ℝ) * log X * sqrt R +
        1000 * X * log X * R + 1001 * log X ^ 2) ≤
      a * T / X ^ (5 / 4 : ℝ) * sqrt R + a * (T / X) * R +
        d * T * log X / X ^ 2 := by
    have hne : X ^ (5 / 4 : ℝ) ≠ 0 := (rpow_pos_of_pos hX0 _).ne'
    dsimp [a, d]
    field_simp [hX0.ne', hL0.ne', hne]
    nlinarith only [congrArg (fun z : ℝ => T * sqrt R * z) hpow,
      mul_nonneg (mul_nonneg hT hL0.le) (rpow_nonneg hX0.le (5 / 4 : ℝ))]
  have hnorm : (12 * T / (X ^ 2 * log X)) * (Δ + δ) =
      12 * T * (Δ + δ) / (X ^ 2 * log X) := by ring
  rw [hnorm] at hmul
  linarith [hmul.trans halg]

/-- Both absorptions, including the log-squared rounding term. -/
theorem scalar_absorption {X E R : ℝ} (hX : 1 < X) (hE : 0 ≤ E) (hR0 : 0 ≤ R)
    (hsmall : a * ((E + 5 * sqrt X) / X) ≤ 1 / 4)
    (hlog : log X ^ 2 ≤ sqrt X)
    (hR : R ≤ a * (E + 5 * sqrt X) / X ^ (5 / 4 : ℝ) * sqrt R +
      a * ((E + 5 * sqrt X) / X) * R +
      d * (E + 5 * sqrt X) * log X / X ^ 2 + 2 / X) :
    R ≤ finalConstant * (E ^ 2 / X ^ (5 / 2 : ℝ) + 1 / X) := by
  have hX0 : 0 < X := by linarith
  have hs0 : 0 < sqrt X := sqrt_pos.mpr hX0
  let T := E + 5 * sqrt X
  let A := X ^ (5 / 4 : ℝ)
  let B := X ^ (3 / 4 : ℝ)
  let Z := T / A
  let Y := log X / B
  have hA : 0 < A := rpow_pos_of_pos hX0 _
  have hB : 0 < B := rpow_pos_of_pos hX0 _
  have hAB : A * B = X ^ 2 := by dsimp [A, B]; rw [← rpow_add hX0]; norm_num
  have hA2 : A ^ 2 = X ^ (5 / 2 : ℝ) := by
    dsimp [A]
    rw [← rpow_mul_natCast hX0.le]
    norm_num
  have hB2 : B ^ 2 = X * sqrt X := by
    dsimp [B]
    rw [← rpow_mul_natCast hX0.le]
    have he : (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 := by norm_num
    rw [he, rpow_add hX0, rpow_one, sqrt_eq_rpow]
  have hZY : Z * Y = T * log X / X ^ 2 := by
    dsimp [Z, Y]
    rw [div_mul_div_comm, hAB]
  have hZ2 : Z ^ 2 = T ^ 2 / X ^ (5 / 2 : ℝ) := by dsimp [Z]; rw [div_pow, hA2]
  have hY2 : Y ^ 2 = log X ^ 2 / (X * sqrt X) := by dsimp [Y]; rw [div_pow, hB2]
  have hYoung : a * Z * sqrt R ≤ R / 4 + a ^ 2 * Z ^ 2 := by
    nlinarith [sq_nonneg (sqrt R / 2 - a * Z), sq_sqrt hR0]
  have hlin := mul_le_mul_of_nonneg_right hsmall hR0
  have hnorm : R ≤ a * Z * sqrt R + a * (T / X) * R + d * Z * Y + 2 / X := by
    change R ≤ a * T / A * sqrt R + a * (T / X) * R + d * T * log X / X ^ 2 + 2 / X at hR
    rw [show a * T / A = a * Z by dsimp [Z]; ring] at hR
    rw [show d * T * log X / X ^ 2 = d * Z * Y by rw [mul_assoc d Z Y, hZY]; ring] at hR
    exact hR
  have htwo : R ≤ 2 * a ^ 2 * Z ^ 2 + 2 * d * Z * Y + 4 / X := by
    change a * (T / X) * R ≤ 1 / 4 * R at hlin
    have hm : R ≤ R / 4 + a ^ 2 * Z ^ 2 + 1 / 4 * R + d * Z * Y + 2 / X :=
      hnorm.trans (add_le_add (add_le_add (add_le_add hYoung hlin) le_rfl) le_rfl)
    let M := a ^ 2 * Z ^ 2 + d * Z * Y + 2 / X
    have he : R / 4 + a ^ 2 * Z ^ 2 + 1 / 4 * R + d * Z * Y + 2 / X = R / 2 + M := by
      dsimp [M]
      ring
    rw [he] at hm
    have hh : R ≤ 2 * M := by linarith only [hm]
    exact hh.trans_eq (by dsimp [M]; ring)
  have hsecond : 2 * Z * Y ≤ Z ^ 2 + Y ^ 2 := by nlinarith only [sq_nonneg (Z - Y)]
  have hd0 : 0 ≤ d := by norm_num [d]
  have hsecondD := mul_le_mul_of_nonneg_left hsecond hd0
  have hq : 0 ≤ q := by norm_num [q, a, d]
  have habsorb : R ≤ q * Z ^ 2 + d * Y ^ 2 + 4 / X := by
    dsimp [q]
    nlinarith only [htwo, hsecondD]
  have hYbound : Y ^ 2 ≤ 1 / X := by
    rw [hY2]
    apply (div_le_div_iff₀ (mul_pos hX0 hs0) hX0).mpr
    simpa only [one_mul, mul_comm X (sqrt X)] using mul_le_mul_of_nonneg_right hlog hX0.le
  have hT2 : T ^ 2 ≤ 2 * E ^ 2 + 50 * X := by
    dsimp [T]
    nlinarith only [sq_nonneg (E - 5 * sqrt X), sq_sqrt hX0.le]
  have hden : X ^ 2 ≤ X ^ (5 / 2 : ℝ) := by
    have hh := rpow_le_rpow_of_exponent_le hX.le (by norm_num : (2 : ℝ) ≤ 5 / 2)
    simpa only [rpow_two] using hh
  have hZbound : Z ^ 2 ≤ 2 * E ^ 2 / X ^ (5 / 2 : ℝ) + 50 / X := by
    rw [hZ2]
    have hden0 := rpow_pos_of_pos hX0 (5 / 2 : ℝ)
    apply (div_le_iff₀ hden0).mpr
    have hratio : 50 * X ≤ 50 / X * X ^ (5 / 2 : ℝ) := by
      have hh : 50 * X ≤ (50 * X ^ (5 / 2 : ℝ)) / X := by
        apply (le_div_iff₀ hX0).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 50)]
      convert hh using 1 <;> ring
    have heq : 2 * E ^ 2 / X ^ (5 / 2 : ℝ) * X ^ (5 / 2 : ℝ) = 2 * E ^ 2 :=
      div_mul_cancel₀ _ hden0.ne'
    nlinarith only [hT2, hratio, heq]
  have hqZ := mul_le_mul_of_nonneg_left hZbound hq
  have hdY := mul_le_mul_of_nonneg_left hYbound hd0
  have hb : R ≤ 2 * q * (E ^ 2 / X ^ (5 / 2 : ℝ)) + (50 * q + d + 4) * (1 / X) := by
    exact (habsorb.trans (add_le_add (add_le_add hqZ hdY) (le_refl (4 / X)))).trans_eq (by ring)
  have hfirst : 2 * q ≤ finalConstant := by norm_num [finalConstant, q, a, d]
  have hlast : 50 * q + d + 4 ≤ finalConstant := by norm_num [finalConstant, q, a, d]
  have hm1 := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ E ^ 2 / X ^ (5 / 2 : ℝ) by positivity)
  have hm2 := mul_le_mul_of_nonneg_right hlast (show 0 ≤ 1 / X by positivity)
  nlinarith only [hb, hm1, hm2]

end D5.S3.Arith.Robin.PriceRecord.HigherLossScalarAbsorption
