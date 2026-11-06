/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows/Row15
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
/-! # Universal exceptional19 residue row 15 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private L rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized floor_on_cell
  from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic

private theorem cell_15_0 (n u : ℕ) (hu : (0 * n + 0) ≤ u ∧ u < (4 * n + 107)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (0 * (n:ℤ) + 0) (4 * (n:ℤ) + 107) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (4 * (n:ℤ) + 107) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (4 * (n:ℤ) + 107) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (4 * (n:ℤ) + 107) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (0 * (n:ℤ) + 0) (4 * (n:ℤ) + 107) 0 u
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

private theorem cell_15_1 (n u : ℕ) (hu : (4 * n + 107) ≤ u ∧ u < (13 * n + 350)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (4 * (n:ℤ) + 107) (13 * (n:ℤ) + 350) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (4 * (n:ℤ) + 107) (13 * (n:ℤ) + 350) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (4 * (n:ℤ) + 107) (13 * (n:ℤ) + 350) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (4 * (n:ℤ) + 107) (13 * (n:ℤ) + 350) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (4 * (n:ℤ) + 107) (13 * (n:ℤ) + 350) 0 u
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

private theorem cell_15_2 (n u : ℕ) (hu : (13 * n + 350) ≤ u ∧ u < (32 * n + 862)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (13 * (n:ℤ) + 350) (32 * (n:ℤ) + 862) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (13 * (n:ℤ) + 350) (32 * (n:ℤ) + 862) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (13 * (n:ℤ) + 350) (32 * (n:ℤ) + 862) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (13 * (n:ℤ) + 350) (32 * (n:ℤ) + 862) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (13 * (n:ℤ) + 350) (32 * (n:ℤ) + 862) 0 u
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

private theorem cell_15_3 (n u : ℕ) (hu : (32 * n + 862) ≤ u ∧ u < (38 * n + 1023)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (32 * (n:ℤ) + 862) (38 * (n:ℤ) + 1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (32 * (n:ℤ) + 862) (38 * (n:ℤ) + 1023) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (32 * (n:ℤ) + 862) (38 * (n:ℤ) + 1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (32 * (n:ℤ) + 862) (38 * (n:ℤ) + 1023) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (32 * (n:ℤ) + 862) (38 * (n:ℤ) + 1023) 0 u
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

private theorem cell_15_4 (n u : ℕ) (hu : (38 * n + 1023) ≤ u ∧ u < (51 * n + 1374)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (38 * (n:ℤ) + 1023) (51 * (n:ℤ) + 1374) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1023) (51 * (n:ℤ) + 1374) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1023) (51 * (n:ℤ) + 1374) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1023) (51 * (n:ℤ) + 1374) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (38 * (n:ℤ) + 1023) (51 * (n:ℤ) + 1374) 1 u
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

private theorem cell_15_5 (n u : ℕ) (hu : (51 * n + 1374) ≤ u ∧ u < (70 * n + 1886)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (51 * (n:ℤ) + 1374) (70 * (n:ℤ) + 1886) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (51 * (n:ℤ) + 1374) (70 * (n:ℤ) + 1886) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (51 * (n:ℤ) + 1374) (70 * (n:ℤ) + 1886) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (51 * (n:ℤ) + 1374) (70 * (n:ℤ) + 1886) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (51 * (n:ℤ) + 1374) (70 * (n:ℤ) + 1886) 1 u
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

private theorem cell_15_6 (n u : ℕ) (hu : (70 * n + 1886) ≤ u ∧ u < (76 * n + 2047)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (70 * (n:ℤ) + 1886) (76 * (n:ℤ) + 2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (70 * (n:ℤ) + 1886) (76 * (n:ℤ) + 2047) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (70 * (n:ℤ) + 1886) (76 * (n:ℤ) + 2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (70 * (n:ℤ) + 1886) (76 * (n:ℤ) + 2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (70 * (n:ℤ) + 1886) (76 * (n:ℤ) + 2047) 1 u
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

private theorem cell_15_7 (n u : ℕ) (hu : (76 * n + 2047) ≤ u ∧ u < (80 * n + 2155)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (76 * (n:ℤ) + 2047) (80 * (n:ℤ) + 2155) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (80 * (n:ℤ) + 2155) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (80 * (n:ℤ) + 2155) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (80 * (n:ℤ) + 2155) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (76 * (n:ℤ) + 2047) (80 * (n:ℤ) + 2155) 2 u
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

private theorem cell_15_8 (n u : ℕ) (hu : (80 * n + 2155) ≤ u ∧ u < (89 * n + 2397)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (80 * (n:ℤ) + 2155) (89 * (n:ℤ) + 2397) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (80 * (n:ℤ) + 2155) (89 * (n:ℤ) + 2397) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (80 * (n:ℤ) + 2155) (89 * (n:ℤ) + 2397) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (80 * (n:ℤ) + 2155) (89 * (n:ℤ) + 2397) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (80 * (n:ℤ) + 2155) (89 * (n:ℤ) + 2397) 2 u
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

private theorem cell_15_9 (n u : ℕ) (hu : (89 * n + 2397) ≤ u ∧ u < (108 * n + 2909)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (89 * (n:ℤ) + 2397) (108 * (n:ℤ) + 2909) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 11 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (89 * (n:ℤ) + 2397) (108 * (n:ℤ) + 2909) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (89 * (n:ℤ) + 2397) (108 * (n:ℤ) + 2909) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (89 * (n:ℤ) + 2397) (108 * (n:ℤ) + 2909) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (89 * (n:ℤ) + 2397) (108 * (n:ℤ) + 2909) 2 u
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

private theorem cell_15_10 (n u : ℕ) (hu : (108 * n + 2909) ≤ u ∧ u < (114 * n + 3071)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (108 * (n:ℤ) + 2909) (114 * (n:ℤ) + 3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 12 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (108 * (n:ℤ) + 2909) (114 * (n:ℤ) + 3071) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (108 * (n:ℤ) + 2909) (114 * (n:ℤ) + 3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (108 * (n:ℤ) + 2909) (114 * (n:ℤ) + 3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (108 * (n:ℤ) + 2909) (114 * (n:ℤ) + 3071) 2 u
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

private theorem cell_15_11 (n u : ℕ) (hu : (114 * n + 3071) ≤ u ∧ u < (127 * n + 3421)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (114 * (n:ℤ) + 3071) (127 * (n:ℤ) + 3421) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 12 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (127 * (n:ℤ) + 3421) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (127 * (n:ℤ) + 3421) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (127 * (n:ℤ) + 3421) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (114 * (n:ℤ) + 3071) (127 * (n:ℤ) + 3421) 3 u
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

private theorem cell_15_12 (n u : ℕ) (hu : (127 * n + 3421) ≤ u ∧ u < (146 * n + 3933)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (127 * (n:ℤ) + 3421) (146 * (n:ℤ) + 3933) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 13 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (127 * (n:ℤ) + 3421) (146 * (n:ℤ) + 3933) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (127 * (n:ℤ) + 3421) (146 * (n:ℤ) + 3933) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (127 * (n:ℤ) + 3421) (146 * (n:ℤ) + 3933) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (127 * (n:ℤ) + 3421) (146 * (n:ℤ) + 3933) 3 u
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

private theorem cell_15_13 (n u : ℕ) (hu : (146 * n + 3933) ≤ u ∧ u < (152 * n + 4095)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15))/(19 * (152 * ((n:ℤ) + 27)-8)) = 5 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 15) (19 * (152 * ((n:ℤ) + 27)-8)) (146 * (n:ℤ) + 3933) (152 * (n:ℤ) + 4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 14 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (146 * (n:ℤ) + 3933) (152 * (n:ℤ) + 4095) 14 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (146 * (n:ℤ) + 3933) (152 * (n:ℤ) + 4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (146 * (n:ℤ) + 3933) (152 * (n:ℤ) + 4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 15 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (146 * (n:ℤ) + 3933) (152 * (n:ℤ) + 4095) 3 u
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

private theorem row_count_15 (n : ℕ) :
    rowZeroCount (n + 27) 15 = 90 * n + 2426 := by
  classical
  have hval (u : ℕ) : rowValue (n + 27) 15 u =
      normalizedRow (152 * ((n:ℤ) + 27)-8) u 15 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using rowValue_normalized (n + 27) 15 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n + 27))).filter
      (fun u : ℕ => normalizedRow (152 * ((n:ℤ) + 27)-8) u 15=0) = ((((((((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ)) ∪ (Finset.Ico (89 * n + 2397) (108 * n + 2909) : Finset ℕ)) ∪ (Finset.Ico (108 * n + 2909) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (127 * n + 3421) (146 * n + 3933) : Finset ℕ)) ∪ (Finset.Ico (146 * n + 3933) (152 * n + 4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n + 27)
    · have hub : u < (152 * n + 4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (4 * n + 107)
      · have hf := cell_15_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at  *
        omega
      · by_cases hc1 : u < (13 * n + 350)
        · have hf := cell_15_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at  *
          omega
        · by_cases hc2 : u < (32 * n + 862)
          · have hf := cell_15_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at  *
            omega
          · by_cases hc3 : u < (38 * n + 1023)
            · have hf := cell_15_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at  *
              omega
            · by_cases hc4 : u < (51 * n + 1374)
              · have hf := cell_15_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at  *
                omega
              · by_cases hc5 : u < (70 * n + 1886)
                · have hf := cell_15_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at  *
                  omega
                · by_cases hc6 : u < (76 * n + 2047)
                  · have hf := cell_15_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at  *
                    omega
                  · by_cases hc7 : u < (80 * n + 2155)
                    · have hf := cell_15_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at  *
                      omega
                    · by_cases hc8 : u < (89 * n + 2397)
                      · have hf := cell_15_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at  *
                        omega
                      · by_cases hc9 : u < (108 * n + 2909)
                        · have hf := cell_15_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at  *
                          omega
                        · by_cases hc10 : u < (114 * n + 3071)
                          · have hf := cell_15_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at  *
                            omega
                          · by_cases hc11 : u < (127 * n + 3421)
                            · have hf := cell_15_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at  *
                              omega
                            · by_cases hc12 : u < (146 * n + 3933)
                              · have hf := cell_15_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
                              · have hf := cell_15_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
    · dsimp [L] at  *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ)) (Finset.Ico (89 * n + 2397) (108 * n + 2909) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ)) ∪ (Finset.Ico (89 * n + 2397) (108 * n + 2909) : Finset ℕ)) (Finset.Ico (108 * n + 2909) (114 * n + 3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ)) ∪ (Finset.Ico (89 * n + 2397) (108 * n + 2909) : Finset ℕ)) ∪ (Finset.Ico (108 * n + 2909) (114 * n + 3071) : Finset ℕ)) (Finset.Ico (127 * n + 3421) (146 * n + 3933) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0 * n + 0) (4 * n + 107) : Finset ℕ) ∪ (Finset.Ico (13 * n + 350) (32 * n + 862) : Finset ℕ)) ∪ (Finset.Ico (38 * n + 1023) (51 * n + 1374) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (80 * n + 2155) : Finset ℕ)) ∪ (Finset.Ico (89 * n + 2397) (108 * n + 2909) : Finset ℕ)) ∪ (Finset.Ico (108 * n + 2909) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (127 * n + 3421) (146 * n + 3933) : Finset ℕ)) (Finset.Ico (146 * n + 3933) (152 * n + 4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
