/- GID: D5/S3/Quantum/Semigroups/WuCubicHellingerReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicHellingerReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two signed spectral tests imply the physical Wu cubic Hellinger margin. -/

import D5.S3.Quantum.Semigroups.WuCubicHellingerCut
import D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients
import OmegaBuild.Commands

/-! Wu v1 (3.54) at equal caps and exponent three. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuCubicHellingerReplay

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicGibbsScaledCoefficients
open WuCubicHellingerCut (hellinger_deficit_bound)
open WuCubicOccupationTaylor (gibbsLevels occupationTaylorCoefficient
  occupation_taylor_lower_bound)

/-- A rational choice for the determinant hypothesis when its linear
coefficient is positive. -/
private theorem rational_eta_admissible {P₀ P₂ κ R : ℝ} (hP₀ : 0 < P₀) (hP₂ : 0 < P₂) :
    let k := (P₀ - P₂) / (P₀ + P₂)
    let B := 4 * κ - k * R
    let η := R ^ 2 / (4 * B)
    0 < B → 0 ≤ η ∧ 0 ≤ (1 - k ^ 2) * η ^ 2 + B * η - R ^ 2 / 4 := by
  intro k B η hB
  have hp := add_pos hP₀ hP₂
  have hk₁ : k ≤ 1 := (div_le_iff₀ hp).2 (by linarith only [hP₂])
  have hk₂ : -1 ≤ k := (le_div_iff₀ hp).2 (by linarith only [hP₀])
  have hk : 0 ≤ 1 - k ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hk₁) (show 0 ≤ 1 + k by linarith only [hk₂])
    nlinarith only [h]
  have hη : 0 ≤ η := div_nonneg (sq_nonneg R) (show 0 ≤ 4 * B by positivity)
  have hcancel : B * η = R ^ 2 / 4 := by
    dsimp only [η]
    field_simp [hB.ne']
  refine ⟨hη, ?_⟩
  rw [hcancel, add_sub_cancel_right]
  exact mul_nonneg hk (sq_nonneg η)

private theorem rational_eta_small {P₀ P₂ κ R : ℝ}
    (hP₀ : 0 < P₀) (hP₂ : 0 < P₂) (hlong : 4 * |R| < 4 * κ) :
    let k := (P₀ - P₂) / (P₀ + P₂)
    let B := 4 * κ - k * R
    let η := R ^ 2 / (4 * B)
    0 < B ∧ 2 * η ≤ |R| / 6 := by
  intro k B η
  have hp := add_pos hP₀ hP₂
  have hk : |k| < 1 := abs_lt.mpr
    ⟨(lt_div_iff₀ hp).mpr (by linarith only [hP₀]),
      (div_lt_iff₀ hp).mpr (by linarith only [hP₂])⟩
  have hkR : k * R ≤ |R| := calc
    _ ≤ |k * R| := le_abs_self _
    _ = |k| * |R| := abs_mul _ _
    _ ≤ |R| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (abs_nonneg R)
  have hBabs : 3 * |R| < B := by
    dsimp only [B]
    linarith only [hlong, hkR]
  have hB : 0 < B := by linarith only [hBabs, abs_nonneg R]
  refine ⟨hB, ?_⟩
  calc
    2 * η = |R| ^ 2 / (2 * B) := by
      rw [sq_abs]
      dsimp only [η]
      field_simp [hB.ne']
      ring
    _ ≤ |R| / 6 := by
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hB)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hBabs.le (abs_nonneg R)]

private theorem hellinger_loss_sq_le {η G R C : ℝ} (hη : 2 * η ≤ |R| / 6)
    (hminus : (G - R / 6) ^ 2 ≤ C) (hplus : (G + R / 6) ^ 2 ≤ C) :
    (max 0 (2 * η - G)) ^ 2 ≤ C := by
  have hsquare (s : ℝ) (hs : 2 * η - G ≤ -s) (hC : s ^ 2 ≤ C) :
      (max 0 (2 * η - G)) ^ 2 ≤ C := by
    have hmax : max 0 (2 * η - G) ≤ |s| :=
      max_le (abs_nonneg s) (hs.trans (neg_le_abs s))
    calc
      _ ≤ |s| ^ 2 := (sq_le_sq₀ (le_max_left _ _) (abs_nonneg s)).mpr hmax
      _ = s ^ 2 := sq_abs s
      _ ≤ C := hC
  rcases le_total 0 R with hR | hR
  · rw [abs_of_nonneg hR] at hη
    exact hsquare (G - R / 6) (by linarith only [hη]) hminus
  · rw [abs_of_nonpos hR] at hη
    exact hsquare (G + R / 6) (by linarith only [hη]) hplus

/-- The two signed tests are the final replay forms evaluated on the direction
`(h 0, (h 1 + h 2 - h 0) / 2, (h 2 - h 1) / 2)` in the replay basis.
The replay divides `P₀`, `P₂` and `4κ` by `(r-1)^2` and the scaled
endpoint slopes by `r-1`. Multiplying each signed form by `(r-1)^6`
gives the tests below. The signed debit keeps the replay's orientation.
The long-crossing pair gives `4 * |R| < 4 * κ` by clearing the positive
weight `p` and the common factor `(r-1)^4`, using
`p * R = 2 * (P₂ * G₀ - P₀ * G₂)`. -/
theorem normalized_deficit_ge_of_signed_forms {r d : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hd : 0 ≤ d) (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (h₀ : 0 ≤ h 0) (h₁₂ : h 1 ≤ h 2)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    let m := x 0
    let n := x 1
    let q := x 2
    let E := cutEnergy r m n q
    let F := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture E F
    let κ := longCoeff r m n q / 4
    let P₀ := (E 0 + Z₀ - L₀) / 2
    let P₂ := (E 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂
    let k := (P₀ - P₂) / p
    let j := P₀ * P₂ / p - L₀ / 4
    let G₀ := F 0 / 2 - 2 * P₀
    let G₂ := F 2 / 2 - 2 * P₂
    let Gs := G₀ + G₂
    let R := G₀ - G₂ - k * Gs
    let g₀ := g0scaled r d h
    let g₂ := g2scaled r d h
    let gs := g₀ + g₂
    let z := (P₂ * g₀ - P₀ * g₂) / 3
    let O := occupationTaylorCoefficient r d h
    let N := ∑ i, h i ^ 2
    let debit := N / 64 + (3 / 2) * h 0 * (h 2 - h 1)
    m ≤ n → n ≤ q → q ≤ 1 →
    0 ≤ L₀ → L₀ ≤ Z₀ → L₀ ≤ Z₂ → 0 < P₀ → 0 < P₂ → 0 ≤ j →
    4 * |R| < 4 * κ →
    (p * gs - z) ^ 2 ≤ 4 * p ^ 3 * (O - debit) →
    (p * gs + z) ^ 2 ≤ 4 * p ^ 3 * (O - debit) →
    (d ^ 2 / 64) * N ≤ normalizedDeficit r U m n q := by
  intro x m n q E F Z₀ Z₂ L₀ κ P₀ P₂ p k j G₀ G₂ Gs R g₀ g₂ gs z O N debit
    hmn hnq hq1 hL₀ hleft hright hP₀ hP₂ hj hlong hminus hplus
  have hp : 0 < p := add_pos hP₀ hP₂
  have hκ : 0 < κ := by linarith only [hlong, abs_nonneg R]
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hcosts : G₀ = d * g₀ ∧ G₂ = d * g₂ := gibbs_endpoint_linear_costs_eq hrpos d h hh
  obtain ⟨hG₀, hG₂⟩ := hcosts
  let ρ := g₀ - g₂ - k * gs
  have hGs : Gs = d * gs := by
    dsimp only [Gs, gs]
    rw [hG₀, hG₂]
    ring
  have hR : R = d * ρ := by
    dsimp only [R, ρ]
    rw [hGs, hG₀, hG₂]
    ring
  have hpk : p * k = P₀ - P₂ := by
    change p * ((P₀ - P₂) / p) = _
    field_simp [hp.ne'] <;> ring
  have hz : p * (ρ / 6) = z := calc
    _ = (p * g₀ - p * g₂ - (p * k) * gs) / 6 := by dsimp only [ρ]; ring
    _ = _ := by rw [hpk]; dsimp only [p, gs, z]; ring
  have hform (a : ℝ) (ha : (p * a) ^ 2 ≤ 4 * p ^ 3 * (O - debit)) :
      a ^ 2 ≤ 4 * p * (O - debit) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hp 2)).mp
    nlinarith only [ha]
  have hsigns : (Gs - R / 6) ^ 2 ≤ d ^ 2 * (4 * p * (O - debit)) ∧
      (Gs + R / 6) ^ 2 ≤ d ^ 2 * (4 * p * (O - debit)) := by
    have hm := hform (gs - ρ / 6) (by rwa [mul_sub, hz])
    have hq := hform (gs + ρ / 6) (by rwa [mul_add, hz])
    rw [hGs, hR]
    constructor
    · calc
        (d * gs - d * ρ / 6) ^ 2 = d ^ 2 * (gs - ρ / 6) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (sq_nonneg d)
    · calc
        (d * gs + d * ρ / 6) ^ 2 = d ^ 2 * (gs + ρ / 6) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (sq_nonneg d)
  let B := 4 * κ - k * R
  let η := R ^ 2 / (4 * B)
  have heta : 0 < B ∧ 2 * η ≤ |R| / 6 :=
    rational_eta_small (κ := κ) (R := R) hP₀ hP₂ hlong
  obtain ⟨hB, hηsmall⟩ := heta
  have hadm : 0 ≤ η ∧ 0 ≤ (1 - k ^ 2) * η ^ 2 + B * η - R ^ 2 / 4 :=
    rational_eta_admissible (κ := κ) (R := R) hP₀ hP₂ hB
  have hm0 : 0 ≤ m := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 0)
  have hn0 : 0 ≤ n := hm0.trans hmn
  have hq0 : 0 ≤ q := hn0.trans hnq
  have hocc : d ^ 2 * O ≤ occupationDeficit r m n q := by
    rw [← occupation_deficit_eq hr hm0 hn0 hq0]
    exact occupation_taylor_lower_bound (d := d) hr hd h hh hx hg
  have hphysical : occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤
      normalizedDeficit r U m n q :=
    hellinger_deficit_bound (η := η) U hr hm0 hmn hnq hq1 hL₀ hleft hright hP₀ hP₂ hκ hj
      hadm.1 hadm.2
  have hloss : (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤ d ^ 2 * (O - debit) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hp)).mpr
    calc
      _ ≤ d ^ 2 * (4 * p * (O - debit)) := hellinger_loss_sq_le hηsmall hsigns.1 hsigns.2
      _ = _ := by ring
  have hdebit : N / 64 ≤ debit :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) h₀) (sub_nonneg.mpr h₁₂))
  calc
    (d ^ 2 / 64) * N = d ^ 2 * (N / 64) := by ring
    _ ≤ d ^ 2 * debit := mul_le_mul_of_nonneg_left hdebit (sq_nonneg d)
    _ = d ^ 2 * O - d ^ 2 * (O - debit) := by ring
    _ ≤ occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) :=
      sub_le_sub hocc hloss
    _ ≤ _ := hphysical

#print axioms normalized_deficit_ge_of_signed_forms

end D5.S3.Quantum.Semigroups.WuCubicHellingerReplay
