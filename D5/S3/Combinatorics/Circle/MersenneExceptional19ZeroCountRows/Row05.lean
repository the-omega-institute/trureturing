/- GID: D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCountRows/Row05
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic
/-! # Universal exceptional19 residue row 5 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private L rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized floor_on_cell
  from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic

private theorem cell_5_0 (n u : ℕ) (hu : (0 * n + 0) ≤ u ∧ u < (17 * n + 458)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (0 * (n:ℤ) + 0) (17 * (n:ℤ) + 458) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (17 * (n:ℤ) + 458) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (17 * (n:ℤ) + 458) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (17 * (n:ℤ) + 458) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (0 * (n:ℤ) + 0) (17 * (n:ℤ) + 458) 0 u
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

private theorem cell_5_1 (n u : ℕ) (hu : (17 * n + 458) ≤ u ∧ u < (36 * n + 970)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (17 * (n:ℤ) + 458) (36 * (n:ℤ) + 970) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (17 * (n:ℤ) + 458) (36 * (n:ℤ) + 970) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (17 * (n:ℤ) + 458) (36 * (n:ℤ) + 970) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (17 * (n:ℤ) + 458) (36 * (n:ℤ) + 970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (17 * (n:ℤ) + 458) (36 * (n:ℤ) + 970) 0 u
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

private theorem cell_5_2 (n u : ℕ) (hu : (36 * n + 970) ≤ u ∧ u < (38 * n + 1024)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (36 * (n:ℤ) + 970) (38 * (n:ℤ) + 1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (36 * (n:ℤ) + 970) (38 * (n:ℤ) + 1024) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (36 * (n:ℤ) + 970) (38 * (n:ℤ) + 1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (36 * (n:ℤ) + 970) (38 * (n:ℤ) + 1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (36 * (n:ℤ) + 970) (38 * (n:ℤ) + 1024) 0 u
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

private theorem cell_5_3 (n u : ℕ) (hu : (38 * n + 1024) ≤ u ∧ u < (52 * n + 1401)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 1 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (38 * (n:ℤ) + 1024) (52 * (n:ℤ) + 1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (52 * (n:ℤ) + 1401) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (52 * (n:ℤ) + 1401) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (52 * (n:ℤ) + 1401) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (38 * (n:ℤ) + 1024) (52 * (n:ℤ) + 1401) 1 u
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

private theorem cell_5_4 (n u : ℕ) (hu : (52 * n + 1401) ≤ u ∧ u < (55 * n + 1482)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (52 * (n:ℤ) + 1401) (55 * (n:ℤ) + 1482) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (52 * (n:ℤ) + 1401) (55 * (n:ℤ) + 1482) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (52 * (n:ℤ) + 1401) (55 * (n:ℤ) + 1482) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (52 * (n:ℤ) + 1401) (55 * (n:ℤ) + 1482) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (52 * (n:ℤ) + 1401) (55 * (n:ℤ) + 1482) 1 u
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

private theorem cell_5_5 (n u : ℕ) (hu : (55 * n + 1482) ≤ u ∧ u < (74 * n + 1994)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (55 * (n:ℤ) + 1482) (74 * (n:ℤ) + 1994) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (55 * (n:ℤ) + 1482) (74 * (n:ℤ) + 1994) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (55 * (n:ℤ) + 1482) (74 * (n:ℤ) + 1994) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (55 * (n:ℤ) + 1482) (74 * (n:ℤ) + 1994) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (55 * (n:ℤ) + 1482) (74 * (n:ℤ) + 1994) 1 u
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

private theorem cell_5_6 (n u : ℕ) (hu : (74 * n + 1994) ≤ u ∧ u < (76 * n + 2048)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (74 * (n:ℤ) + 1994) (76 * (n:ℤ) + 2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (74 * (n:ℤ) + 1994) (76 * (n:ℤ) + 2048) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (74 * (n:ℤ) + 1994) (76 * (n:ℤ) + 2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (74 * (n:ℤ) + 1994) (76 * (n:ℤ) + 2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (74 * (n:ℤ) + 1994) (76 * (n:ℤ) + 2048) 1 u
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

private theorem cell_5_7 (n u : ℕ) (hu : (76 * n + 2048) ≤ u ∧ u < (93 * n + 2506)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (76 * (n:ℤ) + 2048) (93 * (n:ℤ) + 2506) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (93 * (n:ℤ) + 2506) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (93 * (n:ℤ) + 2506) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2048) (93 * (n:ℤ) + 2506) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (76 * (n:ℤ) + 2048) (93 * (n:ℤ) + 2506) 2 u
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

private theorem cell_5_8 (n u : ℕ) (hu : (93 * n + 2506) ≤ u ∧ u < (112 * n + 3018)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (93 * (n:ℤ) + 2506) (112 * (n:ℤ) + 3018) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (93 * (n:ℤ) + 2506) (112 * (n:ℤ) + 3018) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (93 * (n:ℤ) + 2506) (112 * (n:ℤ) + 3018) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (93 * (n:ℤ) + 2506) (112 * (n:ℤ) + 3018) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (93 * (n:ℤ) + 2506) (112 * (n:ℤ) + 3018) 2 u
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

private theorem cell_5_9 (n u : ℕ) (hu : (112 * n + 3018) ≤ u ∧ u < (114 * n + 3071)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (112 * (n:ℤ) + 3018) (114 * (n:ℤ) + 3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (112 * (n:ℤ) + 3018) (114 * (n:ℤ) + 3071) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (112 * (n:ℤ) + 3018) (114 * (n:ℤ) + 3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (112 * (n:ℤ) + 3018) (114 * (n:ℤ) + 3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (112 * (n:ℤ) + 3018) (114 * (n:ℤ) + 3071) 2 u
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

private theorem cell_5_10 (n u : ℕ) (hu : (114 * n + 3071) ≤ u ∧ u < (128 * n + 3449)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (114 * (n:ℤ) + 3071) (128 * (n:ℤ) + 3449) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (128 * (n:ℤ) + 3449) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (128 * (n:ℤ) + 3449) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (128 * (n:ℤ) + 3449) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (114 * (n:ℤ) + 3071) (128 * (n:ℤ) + 3449) 3 u
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

private theorem cell_5_11 (n u : ℕ) (hu : (128 * n + 3449) ≤ u ∧ u < (131 * n + 3529)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (128 * (n:ℤ) + 3449) (131 * (n:ℤ) + 3529) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (128 * (n:ℤ) + 3449) (131 * (n:ℤ) + 3529) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (128 * (n:ℤ) + 3449) (131 * (n:ℤ) + 3529) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (128 * (n:ℤ) + 3449) (131 * (n:ℤ) + 3529) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (128 * (n:ℤ) + 3449) (131 * (n:ℤ) + 3529) 3 u
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

private theorem cell_5_12 (n u : ℕ) (hu : (131 * n + 3529) ≤ u ∧ u < (150 * n + 4041)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (131 * (n:ℤ) + 3529) (150 * (n:ℤ) + 4041) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (131 * (n:ℤ) + 3529) (150 * (n:ℤ) + 4041) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (131 * (n:ℤ) + 3529) (150 * (n:ℤ) + 4041) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (131 * (n:ℤ) + 3529) (150 * (n:ℤ) + 4041) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (131 * (n:ℤ) + 3529) (150 * (n:ℤ) + 4041) 3 u
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

private theorem cell_5_13 (n u : ℕ) (hu : (150 * n + 4041) ≤ u ∧ u < (152 * n + 4095)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 5) (19 * (152 * ((n:ℤ) + 27)-8)) (150 * (n:ℤ) + 4041) (152 * (n:ℤ) + 4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (150 * (n:ℤ) + 4041) (152 * (n:ℤ) + 4095) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (150 * (n:ℤ) + 4041) (152 * (n:ℤ) + 4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (150 * (n:ℤ) + 4041) (152 * (n:ℤ) + 4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 5 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (150 * (n:ℤ) + 4041) (152 * (n:ℤ) + 4095) 3 u
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

private theorem row_count_5 (n : ℕ) :
    rowZeroCount (n + 27) 5 = 106 * n + 2857 := by
  classical
  have hval (u : ℕ) : rowValue (n + 27) 5 u =
      normalizedRow (152 * ((n:ℤ) + 27)-8) u 5 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using rowValue_normalized (n + 27) 5 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n + 27))).filter
      (fun u : ℕ => normalizedRow (152 * ((n:ℤ) + 27)-8) u 5=0) = ((((((((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) ∪ (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (93 * n + 2506) (112 * n + 3018) : Finset ℕ)) ∪ (Finset.Ico (114 * n + 3071) (128 * n + 3449) : Finset ℕ)) ∪ (Finset.Ico (131 * n + 3529) (150 * n + 4041) : Finset ℕ)) ∪ (Finset.Ico (150 * n + 4041) (152 * n + 4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n + 27)
    · have hub : u < (152 * n + 4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (17 * n + 458)
      · have hf := cell_5_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at  *
        omega
      · by_cases hc1 : u < (36 * n + 970)
        · have hf := cell_5_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at  *
          omega
        · by_cases hc2 : u < (38 * n + 1024)
          · have hf := cell_5_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at  *
            omega
          · by_cases hc3 : u < (52 * n + 1401)
            · have hf := cell_5_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at  *
              omega
            · by_cases hc4 : u < (55 * n + 1482)
              · have hf := cell_5_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at  *
                omega
              · by_cases hc5 : u < (74 * n + 1994)
                · have hf := cell_5_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at  *
                  omega
                · by_cases hc6 : u < (76 * n + 2048)
                  · have hf := cell_5_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at  *
                    omega
                  · by_cases hc7 : u < (93 * n + 2506)
                    · have hf := cell_5_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at  *
                      omega
                    · by_cases hc8 : u < (112 * n + 3018)
                      · have hf := cell_5_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at  *
                        omega
                      · by_cases hc9 : u < (114 * n + 3071)
                        · have hf := cell_5_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at  *
                          omega
                        · by_cases hc10 : u < (128 * n + 3449)
                          · have hf := cell_5_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at  *
                            omega
                          · by_cases hc11 : u < (131 * n + 3529)
                            · have hf := cell_5_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at  *
                              omega
                            · by_cases hc12 : u < (150 * n + 4041)
                              · have hf := cell_5_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
                              · have hf := cell_5_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
    · dsimp [L] at  *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) ∪ (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ)) (Finset.Ico (93 * n + 2506) (112 * n + 3018) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) ∪ (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (93 * n + 2506) (112 * n + 3018) : Finset ℕ)) (Finset.Ico (114 * n + 3071) (128 * n + 3449) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) ∪ (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (93 * n + 2506) (112 * n + 3018) : Finset ℕ)) ∪ (Finset.Ico (114 * n + 3071) (128 * n + 3449) : Finset ℕ)) (Finset.Ico (131 * n + 3529) (150 * n + 4041) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0 * n + 0) (17 * n + 458) : Finset ℕ) ∪ (Finset.Ico (38 * n + 1024) (52 * n + 1401) : Finset ℕ)) ∪ (Finset.Ico (55 * n + 1482) (74 * n + 1994) : Finset ℕ)) ∪ (Finset.Ico (74 * n + 1994) (76 * n + 2048) : Finset ℕ)) ∪ (Finset.Ico (93 * n + 2506) (112 * n + 3018) : Finset ℕ)) ∪ (Finset.Ico (114 * n + 3071) (128 * n + 3449) : Finset ℕ)) ∪ (Finset.Ico (131 * n + 3529) (150 * n + 4041) : Finset ℕ)) (Finset.Ico (150 * n + 4041) (152 * n + 4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
