/- GID: D5/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh
   mirror-E: none(waiver:elementary-finite-arithmetic)
   anchors: []
   utility: none
   digest: Positive rational-or-irrational two-generator curvature mesh with exact floor endpoints. -/
import Mathlib.Tactic

/-! SOURCE ONLY. UNCOMPILED_UNACCEPTED / RegUNVALIDATED.
No density, irrationality or Diophantine approximation premise occurs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
open Real

/-- Literal floor algorithm, including both zero coefficients and integer
endpoints. The residual is at least δ, even when r / δ is an integer. -/
theorem positive_curvature_floor_mesh {α δ Δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hδα : δ < α)
    (hΔ : 4 * α ^ 2 / δ + 2 * α ≤ Δ) :
    let N : ℤ := ⌊Δ / α⌋
    let r := Δ - ((N : ℝ) - 1) * α
    ∃ A B : ℕ,
      (B : ℤ) = ⌊r / δ⌋ - 1 ∧
      (A : ℤ) = N - 1 - 2 * B ∧
      (A : ℤ) + 2 * B = N - 1 ∧
      (A + B : ℝ) ≤ Δ / α ∧
      δ ≤ Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) ∧
      Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) < 2 * δ := by
  dsimp only
  let N : ℤ := ⌊Δ / α⌋
  let r : ℝ := Δ - ((N : ℝ) - 1) * α
  let q : ℤ := ⌊r / δ⌋
  let B : ℤ := q - 1
  let A : ℤ := N - 1 - 2 * B
  have hNlo : (N : ℝ) ≤ Δ / α := Int.floor_le _
  have hNhi : Δ / α < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have hNlo' := (le_div_iff₀ hα).mp hNlo
  have hNhi' := (div_lt_iff₀ hα).mp hNhi
  have hrlo : α ≤ r := by dsimp [r]; nlinarith only [hNlo']
  have hrhi : r < 2 * α := by dsimp [r]; nlinarith only [hNhi']
  have hqlo : (q : ℝ) ≤ r / δ := Int.floor_le _
  have hqhi : r / δ < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hqlo' := (le_div_iff₀ hδ).mp hqlo
  have hqhi' := (div_lt_iff₀ hδ).mp hqhi
  have hq1 : (1 : ℤ) ≤ q := by
    apply Int.le_floor.mpr
    norm_num only [Int.cast_one]
    exact (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hδα.le.trans hrlo)
  have hB0 : 0 ≤ B := by dsimp [B]; omega
  have hBcast : (B : ℝ) = (q : ℝ) - 1 := by simp [B]
  have hAcast : (A : ℝ) = (N : ℝ) - 1 - 2 * B := by simp [A]
  have hBbound : (B : ℝ) * δ < 2 * α := by
    rw [hBcast]
    nlinarith only [hqlo', hrhi, hδ]
  have hlarge : 4 * α ^ 2 + 2 * α * δ ≤ Δ * δ := by
    have hh := (div_le_iff₀ hδ).mp
      (show 4 * α ^ 2 / δ ≤ Δ - 2 * α by linarith only [hΔ])
    nlinarith only [hh]
  have hNlarge : 4 * α < ((N : ℝ) - 1) * δ := by
    have hm := mul_lt_mul_of_pos_right hNhi' hδ
    have hprod : α * (4 * α - ((N : ℝ) - 1) * δ) < 0 := by
      nlinarith only [hm, hlarge]
    by_contra! hn
    have hh := mul_nonneg hα.le (sub_nonneg.mpr hn)
    linarith only [hh, hprod]
  have hA0 : 0 ≤ A := by
    have hδA : 0 < (A : ℝ) * δ := by
      rw [hAcast]
      nlinarith only [hNlarge, hBbound]
    have hAr : 0 ≤ (A : ℝ) := (pos_of_mul_pos_left hδA hδ.le).le
    exact_mod_cast hAr
  have hAt : ((A.toNat : ℕ) : ℤ) = A := Int.toNat_of_nonneg hA0
  have hBt : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hB0
  have hAtr : ((A.toNat : ℕ) : ℝ) = (A : ℝ) := by exact_mod_cast hAt
  have hBtr : ((B.toNat : ℕ) : ℝ) = (B : ℝ) := by exact_mod_cast hBt
  refine ⟨A.toNat, B.toNat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hBt] using (show B = ⌊r / δ⌋ - 1 from rfl)
  · rw [hAt, hBt]
  · rw [hAt, hBt]
    dsimp [A]
    ring
  · push_cast
    rw [hAtr, hBtr, hAcast]
    have hBr : 0 ≤ (B : ℝ) := by exact_mod_cast hB0
    linarith only [hNlo, hBr]
  · rw [hAtr, hBtr, hAcast, hBcast]
    dsimp [r] at hqlo'
    nlinarith only [hqlo']
  · rw [hAtr, hBtr, hAcast, hBcast]
    dsimp [r] at hqhi'
    nlinarith only [hqhi']

#print axioms positive_curvature_floor_mesh
end D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
