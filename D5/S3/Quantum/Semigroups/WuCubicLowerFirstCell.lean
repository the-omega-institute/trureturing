import D5.S3.Quantum.Semigroups.WuCubicLowerCells
import D5.S3.Quantum.Semigroups.WuCubicLowerPartition

/-! Kernel replay and physical deficit bound for the first lower near-Gibbs leaf. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowerFirstCell

open _root_.Matrix
open scoped BigOperators
open WuCubicLowerOccupation (lowerMatrix normalized_deficit_ge_of_lower_matrix)
open WuCubicLowerCoefficients (offsets radius tests)
open WuCubicLowerJets (pointOffsets)
open WuCubicUpperPartition (Box InBox)
open WuCubicLowerPartition (tree root)
open WuCubicOccupationTaylor (gibbsLevels)
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicHellingerMatrix (displacement levels)

open private padPoint from D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells

def firstLowerCell : Box :=
  ![(1049 / 1000, 67287 / 64000), (-1 / 256, -3 / 1024),
    (-1 / 256, -3 / 1024), (0, 1 / 8)]

set_option maxRecDepth 8192 in
theorem firstLowerCell_is_first :
    (tree.leaves root).take 1 = [firstLowerCell] := by
  decide +kernel

set_option maxHeartbeats 1800000 in
-- The kernel evaluates the rational jets and weighted pivots on one leaf.
theorem firstLowerCell_accepted : WuCubicLowerCells.check firstLowerCell = true := by
  decide +kernel

theorem firstLowerCell_sound {x : Fin 4 → ℝ} (hx : InBox firstLowerCell x) :
    let y := offsets (x 1) (x 2) (x 3)
    (∀ k, 0 < tests (x 0) y k) ∧ (lowerMatrix (x 0) y).PosSemidef := by
  have hy : pointOffsets (padPoint x) = offsets (x 1) (x 2) (x 3) := rfl
  simpa only [hy] using WuCubicLowerCells.check_sound firstLowerCell_accepted hx

theorem normalized_deficit_ge (U : unitary Mat) {x : Fin 4 → ℝ}
    (hx : InBox firstLowerCell x) :
    let r := x 0
    let y := offsets (x 1) (x 2) (x 3)
    ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) / 1024 ≤
      normalizedDeficit r U (levels r y 0) (levels r y 1) (levels r y 2) := by
  intro r y
  have hrange := hx 0
  have ha := hx 1
  have hb := hx 2
  have ht := hx 3
  norm_num [firstLowerCell] at hrange ha hb ht
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 1049 / 1000).trans_le hrange.1
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrhi : r ≤ 6 / 5 := hrange.2.trans (by norm_num)
  have hrlo : 1049 / 1000 ≤ r := hrange.1
  have hcap : (radius : ℝ) = 1 / 256 := by norm_num [radius]
  have hy₀ : y 0 = x 1 := rfl
  have hy₁ : y 1 = x 2 := rfl
  have hy₂ : y 2 = x 2 + (1 / 256 - x 2) * x 3 := by
    change x 2 + ((radius : ℝ) - x 2) * x 3 = _
    rw [hcap]
  have hgap : 0 ≤ (1 / 256 : ℝ) - x 2 := by linarith only [hb.2]
  have hy₁₂ : y 1 ≤ y 2 := by
    rw [hy₁, hy₂]
    exact le_add_of_nonneg_right (mul_nonneg hgap ht.1)
  have hy₂cap : y 2 ≤ 1 / 256 := by
    rw [hy₂]
    linarith only [mul_le_of_le_one_right hgap (ht.2.trans (by norm_num : (1 : ℝ) / 8 ≤ 1))]
  have hrsq := pow_le_pow_left₀ hrpos.le hrhi 2
  have hg₀ := (inv_le_inv₀ (by norm_num : (0 : ℝ) < (6 / 5) ^ 2)
    (pow_pos hrpos 2)).mpr hrsq
  have hg₁ := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 6 / 5) hrpos).mpr hrhi
  have hg₁hi := (inv_le_inv₀ hrpos (by norm_num : (0 : ℝ) < 1049 / 1000)).mpr hrlo
  have hsep : (1 / 256 : ℝ) ≤ r⁻¹ - (r ^ 2)⁻¹ := by
    rw [show r⁻¹ - (r ^ 2)⁻¹ = (r - 1) / r ^ 2 by
      field_simp [hrpos.ne']
      <;> ring]
    exact (le_div_iff₀ (pow_pos hrpos 2)).mpr (by nlinarith only [hrsq, hrlo])
  let h : Fin 4 → ℝ := ![y 0, y 1, y 2, 0]
  have hdisp : displacement 1 h = y := by
    funext i
    fin_cases i <;> simp [displacement, h]
  have hg (i : Fin 4) : 1 / 2 ≤ gibbsLevels r i := by
    fin_cases i <;> norm_num [gibbsLevels] <;> linarith only [hg₀, hg₁]
  have hl (i : Fin 4) : 1 / 2 ≤ gibbsLevels r i + h i := by
    fin_cases i <;> norm_num [gibbsLevels, h] <;>
      linarith only [hg₀, hg₁, ha.1, hb.1, hy₀, hy₁, hy₁₂]
  have hmn : levels r y 0 ≤ levels r y 1 := by
    change (r ^ 2)⁻¹ + y 0 ≤ r⁻¹ + y 1
    linarith only [hsep, ha.2, hb.1, hy₀, hy₁]
  have hnq : levels r y 1 ≤ levels r y 2 := by
    change r⁻¹ + y 1 ≤ r⁻¹ + y 2
    exact add_le_add_right hy₁₂ _
  have hq : levels r y 2 ≤ 1 := by
    change r⁻¹ + y 2 ≤ 1
    linarith only [hg₁hi, hy₂cap]
  have H := normalized_deficit_ge_of_lower_matrix U hr h (by rfl) hl hg
  dsimp only at H
  rw [hdisp] at H
  obtain ⟨htests, hmatrix⟩ := firstLowerCell_sound hx
  simpa [Fin.sum_univ_four, h] using H hmn hnq hq htests hmatrix

#print axioms WuCubicLowerCells.check_sound
#print axioms firstLowerCell_is_first
#print axioms firstLowerCell_accepted
#print axioms normalized_deficit_ge

end D5.S3.Quantum.Semigroups.WuCubicLowerFirstCell
