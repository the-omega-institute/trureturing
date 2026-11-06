/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows/Row11
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
/-! # Universal exceptional19 residue row 11 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private L rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized floor_on_cell
  from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic

private theorem cell_11_0 (n u : ℕ) (hu : (0 * n + 0) ≤ u ∧ u < (7 * n + 189)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (0 * (n:ℤ) + 0) (7 * (n:ℤ) + 189) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (7 * (n:ℤ) + 189) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (7 * (n:ℤ) + 189) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (7 * (n:ℤ) + 189) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (0 * (n:ℤ) + 0) (7 * (n:ℤ) + 189) 0 u
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

private theorem cell_11_1 (n u : ℕ) (hu : (7 * n + 189) ≤ u ∧ u < (8 * n + 215)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (7 * (n:ℤ) + 189) (8 * (n:ℤ) + 215) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (7 * (n:ℤ) + 189) (8 * (n:ℤ) + 215) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (7 * (n:ℤ) + 189) (8 * (n:ℤ) + 215) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (7 * (n:ℤ) + 189) (8 * (n:ℤ) + 215) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (7 * (n:ℤ) + 189) (8 * (n:ℤ) + 215) 0 u
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

private theorem cell_11_2 (n u : ℕ) (hu : (8 * n + 215) ≤ u ∧ u < (26 * n + 700)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (8 * (n:ℤ) + 215) (26 * (n:ℤ) + 700) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (8 * (n:ℤ) + 215) (26 * (n:ℤ) + 700) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (8 * (n:ℤ) + 215) (26 * (n:ℤ) + 700) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (8 * (n:ℤ) + 215) (26 * (n:ℤ) + 700) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (8 * (n:ℤ) + 215) (26 * (n:ℤ) + 700) 0 u
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

private theorem cell_11_3 (n u : ℕ) (hu : (26 * n + 700) ≤ u ∧ u < (38 * n + 1024)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (26 * (n:ℤ) + 700) (38 * (n:ℤ) + 1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (26 * (n:ℤ) + 700) (38 * (n:ℤ) + 1024) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (26 * (n:ℤ) + 700) (38 * (n:ℤ) + 1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (26 * (n:ℤ) + 700) (38 * (n:ℤ) + 1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (26 * (n:ℤ) + 700) (38 * (n:ℤ) + 1024) 0 u
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

private theorem cell_11_4 (n u : ℕ) (hu : (38 * n + 1024) ≤ u ∧ u < (45 * n + 1212)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (38 * (n:ℤ) + 1024) (45 * (n:ℤ) + 1212) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (45 * (n:ℤ) + 1212) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (45 * (n:ℤ) + 1212) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (45 * (n:ℤ) + 1212) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (38 * (n:ℤ) + 1024) (45 * (n:ℤ) + 1212) 1 u
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

private theorem cell_11_5 (n u : ℕ) (hu : (45 * n + 1212) ≤ u ∧ u < (64 * n + 1724)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (45 * (n:ℤ) + 1212) (64 * (n:ℤ) + 1724) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (45 * (n:ℤ) + 1212) (64 * (n:ℤ) + 1724) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (45 * (n:ℤ) + 1212) (64 * (n:ℤ) + 1724) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (45 * (n:ℤ) + 1212) (64 * (n:ℤ) + 1724) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (45 * (n:ℤ) + 1212) (64 * (n:ℤ) + 1724) 1 u
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

private theorem cell_11_6 (n u : ℕ) (hu : (64 * n + 1724) ≤ u ∧ u < (76 * n + 2047)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (64 * (n:ℤ) + 1724) (76 * (n:ℤ) + 2047) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (64 * (n:ℤ) + 1724) (76 * (n:ℤ) + 2047) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (64 * (n:ℤ) + 1724) (76 * (n:ℤ) + 2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (64 * (n:ℤ) + 1724) (76 * (n:ℤ) + 2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (64 * (n:ℤ) + 1724) (76 * (n:ℤ) + 2047) 1 u
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

private theorem cell_11_7 (n u : ℕ) (hu : (76 * n + 2047) ≤ u ∧ u < (83 * n + 2236)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (76 * (n:ℤ) + 2047) (83 * (n:ℤ) + 2236) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (83 * (n:ℤ) + 2236) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (83 * (n:ℤ) + 2236) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (83 * (n:ℤ) + 2236) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (76 * (n:ℤ) + 2047) (83 * (n:ℤ) + 2236) 2 u
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

private theorem cell_11_8 (n u : ℕ) (hu : (83 * n + 2236) ≤ u ∧ u < (84 * n + 2263)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (83 * (n:ℤ) + 2236) (84 * (n:ℤ) + 2263) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (83 * (n:ℤ) + 2236) (84 * (n:ℤ) + 2263) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (83 * (n:ℤ) + 2236) (84 * (n:ℤ) + 2263) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (83 * (n:ℤ) + 2236) (84 * (n:ℤ) + 2263) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (83 * (n:ℤ) + 2236) (84 * (n:ℤ) + 2263) 2 u
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

private theorem cell_11_9 (n u : ℕ) (hu : (84 * n + 2263) ≤ u ∧ u < (102 * n + 2748)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (84 * (n:ℤ) + 2263) (102 * (n:ℤ) + 2748) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (84 * (n:ℤ) + 2263) (102 * (n:ℤ) + 2748) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (84 * (n:ℤ) + 2263) (102 * (n:ℤ) + 2748) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (84 * (n:ℤ) + 2263) (102 * (n:ℤ) + 2748) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (84 * (n:ℤ) + 2263) (102 * (n:ℤ) + 2748) 2 u
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

private theorem cell_11_10 (n u : ℕ) (hu : (102 * n + 2748) ≤ u ∧ u < (114 * n + 3071)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (102 * (n:ℤ) + 2748) (114 * (n:ℤ) + 3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (102 * (n:ℤ) + 2748) (114 * (n:ℤ) + 3071) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (102 * (n:ℤ) + 2748) (114 * (n:ℤ) + 3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (102 * (n:ℤ) + 2748) (114 * (n:ℤ) + 3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (102 * (n:ℤ) + 2748) (114 * (n:ℤ) + 3071) 2 u
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

private theorem cell_11_11 (n u : ℕ) (hu : (114 * n + 3071) ≤ u ∧ u < (121 * n + 3260)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (114 * (n:ℤ) + 3071) (121 * (n:ℤ) + 3260) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (121 * (n:ℤ) + 3260) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (121 * (n:ℤ) + 3260) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (121 * (n:ℤ) + 3260) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (114 * (n:ℤ) + 3071) (121 * (n:ℤ) + 3260) 3 u
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

private theorem cell_11_12 (n u : ℕ) (hu : (121 * n + 3260) ≤ u ∧ u < (140 * n + 3772)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (121 * (n:ℤ) + 3260) (140 * (n:ℤ) + 3772) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 11 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (121 * (n:ℤ) + 3260) (140 * (n:ℤ) + 3772) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (121 * (n:ℤ) + 3260) (140 * (n:ℤ) + 3772) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (121 * (n:ℤ) + 3260) (140 * (n:ℤ) + 3772) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (121 * (n:ℤ) + 3260) (140 * (n:ℤ) + 3772) 3 u
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

private theorem cell_11_13 (n u : ℕ) (hu : (140 * n + 3772) ≤ u ∧ u < (152 * n + 4095)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 11) (19 * (152 * ((n:ℤ) + 27)-8)) (140 * (n:ℤ) + 3772) (152 * (n:ℤ) + 4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 12 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (140 * (n:ℤ) + 3772) (152 * (n:ℤ) + 4095) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (140 * (n:ℤ) + 3772) (152 * (n:ℤ) + 4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (140 * (n:ℤ) + 3772) (152 * (n:ℤ) + 4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 11 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (140 * (n:ℤ) + 3772) (152 * (n:ℤ) + 4095) 3 u
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

private theorem row_count_11 (n : ℕ) :
    rowZeroCount (n + 27) 11 = 124 * n + 3342 := by
  classical
  have hval (u : ℕ) : rowValue (n + 27) 11 u =
      normalizedRow (152 * ((n:ℤ) + 27)-8) u 11 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using rowValue_normalized (n + 27) 11 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n + 27))).filter
      (fun u : ℕ => normalizedRow (152 * ((n:ℤ) + 27)-8) u 11=0) = (((((((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ)) ∪ (Finset.Ico (84 * n + 2263) (102 * n + 2748) : Finset ℕ)) ∪ (Finset.Ico (102 * n + 2748) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (121 * n + 3260) (140 * n + 3772) : Finset ℕ)) ∪ (Finset.Ico (140 * n + 3772) (152 * n + 4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n + 27)
    · have hub : u < (152 * n + 4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (7 * n + 189)
      · have hf := cell_11_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at  *
        omega
      · by_cases hc1 : u < (8 * n + 215)
        · have hf := cell_11_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at  *
          omega
        · by_cases hc2 : u < (26 * n + 700)
          · have hf := cell_11_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at  *
            omega
          · by_cases hc3 : u < (38 * n + 1024)
            · have hf := cell_11_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at  *
              omega
            · by_cases hc4 : u < (45 * n + 1212)
              · have hf := cell_11_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at  *
                omega
              · by_cases hc5 : u < (64 * n + 1724)
                · have hf := cell_11_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at  *
                  omega
                · by_cases hc6 : u < (76 * n + 2047)
                  · have hf := cell_11_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at  *
                    omega
                  · by_cases hc7 : u < (83 * n + 2236)
                    · have hf := cell_11_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at  *
                      omega
                    · by_cases hc8 : u < (84 * n + 2263)
                      · have hf := cell_11_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at  *
                        omega
                      · by_cases hc9 : u < (102 * n + 2748)
                        · have hf := cell_11_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at  *
                          omega
                        · by_cases hc10 : u < (114 * n + 3071)
                          · have hf := cell_11_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at  *
                            omega
                          · by_cases hc11 : u < (121 * n + 3260)
                            · have hf := cell_11_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at  *
                              omega
                            · by_cases hc12 : u < (140 * n + 3772)
                              · have hf := cell_11_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
                              · have hf := cell_11_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
    · dsimp [L] at  *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ)) (Finset.Ico (84 * n + 2263) (102 * n + 2748) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ)) ∪ (Finset.Ico (84 * n + 2263) (102 * n + 2748) : Finset ℕ)) (Finset.Ico (102 * n + 2748) (114 * n + 3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ)) ∪ (Finset.Ico (84 * n + 2263) (102 * n + 2748) : Finset ℕ)) ∪ (Finset.Ico (102 * n + 2748) (114 * n + 3071) : Finset ℕ)) (Finset.Ico (121 * n + 3260) (140 * n + 3772) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0 * n + 0) (7 * n + 189) : Finset ℕ) ∪ (Finset.Ico (8 * n + 215) (26 * n + 700) : Finset ℕ)) ∪ (Finset.Ico (26 * n + 700) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (45 * n + 1212) (64 * n + 1724) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (83 * n + 2236) : Finset ℕ)) ∪ (Finset.Ico (84 * n + 2263) (102 * n + 2748) : Finset ℕ)) ∪ (Finset.Ico (102 * n + 2748) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (121 * n + 3260) (140 * n + 3772) : Finset ℕ)) (Finset.Ico (140 * n + 3772) (152 * n + 4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
