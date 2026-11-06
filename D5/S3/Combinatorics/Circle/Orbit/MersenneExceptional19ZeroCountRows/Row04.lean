/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows/Row04
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
/-! # Universal exceptional19 residue row 4 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private L rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized floor_on_cell
  from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic

private theorem cell_4_0 (n u : ℕ) (hu : (0 * n + 0) ≤ u ∧ u < (6 * n + 162)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (0 * (n:ℤ) + 0) (6 * (n:ℤ) + 162) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (6 * (n:ℤ) + 162) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (6 * (n:ℤ) + 162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (6 * (n:ℤ) + 162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (0 * (n:ℤ) + 0) (6 * (n:ℤ) + 162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_1 (n u : ℕ) (hu : (6 * n + 162) ≤ u ∧ u < (25 * n + 674)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (6 * (n:ℤ) + 162) (25 * (n:ℤ) + 674) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (6 * (n:ℤ) + 162) (25 * (n:ℤ) + 674) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (6 * (n:ℤ) + 162) (25 * (n:ℤ) + 674) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (6 * (n:ℤ) + 162) (25 * (n:ℤ) + 674) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (6 * (n:ℤ) + 162) (25 * (n:ℤ) + 674) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_2 (n u : ℕ) (hu : (25 * n + 674) ≤ u ∧ u < (38 * n + 1024)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (25 * (n:ℤ) + 674) (38 * (n:ℤ) + 1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (25 * (n:ℤ) + 674) (38 * (n:ℤ) + 1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (25 * (n:ℤ) + 674) (38 * (n:ℤ) + 1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (25 * (n:ℤ) + 674) (38 * (n:ℤ) + 1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (25 * (n:ℤ) + 674) (38 * (n:ℤ) + 1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_3 (n u : ℕ) (hu : (38 * n + 1024) ≤ u ∧ u < (44 * n + 1186)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (38 * (n:ℤ) + 1024) (44 * (n:ℤ) + 1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (44 * (n:ℤ) + 1186) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (44 * (n:ℤ) + 1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (44 * (n:ℤ) + 1186) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (38 * (n:ℤ) + 1024) (44 * (n:ℤ) + 1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_4 (n u : ℕ) (hu : (44 * n + 1186) ≤ u ∧ u < (63 * n + 1698)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (44 * (n:ℤ) + 1186) (63 * (n:ℤ) + 1698) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (44 * (n:ℤ) + 1186) (63 * (n:ℤ) + 1698) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (44 * (n:ℤ) + 1186) (63 * (n:ℤ) + 1698) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (44 * (n:ℤ) + 1186) (63 * (n:ℤ) + 1698) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (44 * (n:ℤ) + 1186) (63 * (n:ℤ) + 1698) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_5 (n u : ℕ) (hu : (63 * n + 1698) ≤ u ∧ u < (72 * n + 1940)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (63 * (n:ℤ) + 1698) (72 * (n:ℤ) + 1940) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (63 * (n:ℤ) + 1698) (72 * (n:ℤ) + 1940) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (63 * (n:ℤ) + 1698) (72 * (n:ℤ) + 1940) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (63 * (n:ℤ) + 1698) (72 * (n:ℤ) + 1940) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (63 * (n:ℤ) + 1698) (72 * (n:ℤ) + 1940) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_6 (n u : ℕ) (hu : (72 * n + 1940) ≤ u ∧ u < (76 * n + 2048)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2048) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_7 (n u : ℕ) (hu : (76 * n + 2048) ≤ u ∧ u < (82 * n + 2209)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (76 * (n:ℤ) + 2048) (82 * (n:ℤ) + 2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (82 * (n:ℤ) + 2209) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (82 * (n:ℤ) + 2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (82 * (n:ℤ) + 2209) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (76 * (n:ℤ) + 2048) (82 * (n:ℤ) + 2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_8 (n u : ℕ) (hu : (82 * n + 2209) ≤ u ∧ u < (101 * n + 2721)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (82 * (n:ℤ) + 2209) (101 * (n:ℤ) + 2721) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (82 * (n:ℤ) + 2209) (101 * (n:ℤ) + 2721) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (82 * (n:ℤ) + 2209) (101 * (n:ℤ) + 2721) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (82 * (n:ℤ) + 2209) (101 * (n:ℤ) + 2721) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (82 * (n:ℤ) + 2209) (101 * (n:ℤ) + 2721) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_9 (n u : ℕ) (hu : (101 * n + 2721) ≤ u ∧ u < (114 * n + 3072)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (101 * (n:ℤ) + 2721) (114 * (n:ℤ) + 3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (101 * (n:ℤ) + 2721) (114 * (n:ℤ) + 3072) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (101 * (n:ℤ) + 2721) (114 * (n:ℤ) + 3072) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (101 * (n:ℤ) + 2721) (114 * (n:ℤ) + 3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (101 * (n:ℤ) + 2721) (114 * (n:ℤ) + 3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_10 (n u : ℕ) (hu : (114 * n + 3072) ≤ u ∧ u < (120 * n + 3233)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (114 * (n:ℤ) + 3072) (120 * (n:ℤ) + 3233) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3072) (120 * (n:ℤ) + 3233) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3072) (120 * (n:ℤ) + 3233) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3072) (120 * (n:ℤ) + 3233) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (114 * (n:ℤ) + 3072) (120 * (n:ℤ) + 3233) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_11 (n u : ℕ) (hu : (120 * n + 3233) ≤ u ∧ u < (139 * n + 3745)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (120 * (n:ℤ) + 3233) (139 * (n:ℤ) + 3745) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (120 * (n:ℤ) + 3233) (139 * (n:ℤ) + 3745) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (120 * (n:ℤ) + 3233) (139 * (n:ℤ) + 3745) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (120 * (n:ℤ) + 3233) (139 * (n:ℤ) + 3745) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (120 * (n:ℤ) + 3233) (139 * (n:ℤ) + 3745) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_12 (n u : ℕ) (hu : (139 * n + 3745) ≤ u ∧ u < (148 * n + 3988)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (139 * (n:ℤ) + 3745) (148 * (n:ℤ) + 3988) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (139 * (n:ℤ) + 3745) (148 * (n:ℤ) + 3988) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (139 * (n:ℤ) + 3745) (148 * (n:ℤ) + 3988) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (139 * (n:ℤ) + 3745) (148 * (n:ℤ) + 3988) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (139 * (n:ℤ) + 3745) (148 * (n:ℤ) + 3988) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_13 (n u : ℕ) (hu : (148 * n + 3988) ≤ u ∧ u < (152 * n + 4095)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 4) (19 * (152 * ((n:ℤ) + 27)-8)) (148 * (n:ℤ) + 3988) (152 * (n:ℤ) + 4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3988) (152 * (n:ℤ) + 4095) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3988) (152 * (n:ℤ) + 4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3988) (152 * (n:ℤ) + 4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 4 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (148 * (n:ℤ) + 3988) (152 * (n:ℤ) + 4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_4 (n : ℕ) :
    rowZeroCount (n + 27) 4 = 90 * n + 2426 := by
  classical
  have hval (u : ℕ) : rowValue (n + 27) 4 u =
      normalizedRow (152 * ((n:ℤ) + 27)-8) u 4 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using rowValue_normalized (n + 27) 4 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n + 27))).filter
      (fun u : ℕ => normalizedRow (152 * ((n:ℤ) + 27)-8) u 4=0) = ((((((((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) ∪ (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ)) ∪ (Finset.Ico (72 * n + 1940) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (101 * n + 2721) (114 * n + 3072) : Finset ℕ)) ∪ (Finset.Ico (120 * n + 3233) (139 * n + 3745) : Finset ℕ)) ∪ (Finset.Ico (148 * n + 3988) (152 * n + 4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n + 27)
    · have hub : u < (152 * n + 4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (6 * n + 162)
      · have hf := cell_4_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at  *
        omega
      · by_cases hc1 : u < (25 * n + 674)
        · have hf := cell_4_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at  *
          omega
        · by_cases hc2 : u < (38 * n + 1024)
          · have hf := cell_4_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at  *
            omega
          · by_cases hc3 : u < (44 * n + 1186)
            · have hf := cell_4_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at  *
              omega
            · by_cases hc4 : u < (63 * n + 1698)
              · have hf := cell_4_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at  *
                omega
              · by_cases hc5 : u < (72 * n + 1940)
                · have hf := cell_4_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at  *
                  omega
                · by_cases hc6 : u < (76 * n + 2048)
                  · have hf := cell_4_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at  *
                    omega
                  · by_cases hc7 : u < (82 * n + 2209)
                    · have hf := cell_4_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at  *
                      omega
                    · by_cases hc8 : u < (101 * n + 2721)
                      · have hf := cell_4_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at  *
                        omega
                      · by_cases hc9 : u < (114 * n + 3072)
                        · have hf := cell_4_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at  *
                          omega
                        · by_cases hc10 : u < (120 * n + 3233)
                          · have hf := cell_4_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at  *
                            omega
                          · by_cases hc11 : u < (139 * n + 3745)
                            · have hf := cell_4_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at  *
                              omega
                            · by_cases hc12 : u < (148 * n + 3988)
                              · have hf := cell_4_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
                              · have hf := cell_4_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
    · dsimp [L] at  *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) ∪ (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ)) (Finset.Ico (72 * n + 1940) (76 * n + 2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) ∪ (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ)) ∪ (Finset.Ico (72 * n + 1940) (76 * n + 2048) : Finset ℕ)) (Finset.Ico (101 * n + 2721) (114 * n + 3072) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) ∪ (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ)) ∪ (Finset.Ico (72 * n + 1940) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (101 * n + 2721) (114 * n + 3072) : Finset ℕ)) (Finset.Ico (120 * n + 3233) (139 * n + 3745) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0 * n + 0) (6 * n + 162) : Finset ℕ) ∪ (Finset.Ico (6 * n + 162) (25 * n + 674) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1024) (44 * n + 1186) : Finset ℕ)) ∪ (Finset.Ico (44 * n + 1186) (63 * n + 1698) : Finset ℕ)) ∪ (Finset.Ico (72 * n + 1940) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (101 * n + 2721) (114 * n + 3072) : Finset ℕ)) ∪ (Finset.Ico (120 * n + 3233) (139 * n + 3745) : Finset ℕ)) (Finset.Ico (148 * n + 3988) (152 * n + 4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
