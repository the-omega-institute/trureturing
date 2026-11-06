/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows/Row10
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
/-! # Universal exceptional19 residue row 10 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
open private L rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized floor_on_cell
  from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic

private theorem cell_10_0 (n u : ℕ) (hu : (0 * n + 0) ≤ u ∧ u < (15 * n + 404)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (0 * (n:ℤ) + 0) (15 * (n:ℤ) + 404) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (15 * (n:ℤ) + 404) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (15 * (n:ℤ) + 404) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (0 * (n:ℤ) + 0) (15 * (n:ℤ) + 404) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (0 * (n:ℤ) + 0) (15 * (n:ℤ) + 404) 0 u
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

private theorem cell_10_1 (n u : ℕ) (hu : (15 * n + 404) ≤ u ∧ u < (28 * n + 754)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 2 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (15 * (n:ℤ) + 404) (28 * (n:ℤ) + 754) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (15 * (n:ℤ) + 404) (28 * (n:ℤ) + 754) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (15 * (n:ℤ) + 404) (28 * (n:ℤ) + 754) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (15 * (n:ℤ) + 404) (28 * (n:ℤ) + 754) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (15 * (n:ℤ) + 404) (28 * (n:ℤ) + 754) 0 u
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

private theorem cell_10_2 (n u : ℕ) (hu : (28 * n + 754) ≤ u ∧ u < (34 * n + 916)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (28 * (n:ℤ) + 754) (34 * (n:ℤ) + 916) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (28 * (n:ℤ) + 754) (34 * (n:ℤ) + 916) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (28 * (n:ℤ) + 754) (34 * (n:ℤ) + 916) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (28 * (n:ℤ) + 754) (34 * (n:ℤ) + 916) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (28 * (n:ℤ) + 754) (34 * (n:ℤ) + 916) 0 u
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

private theorem cell_10_3 (n u : ℕ) (hu : (34 * n + 916) ≤ u ∧ u < (38 * n + 1024)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (34 * (n:ℤ) + 916) (38 * (n:ℤ) + 1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (34 * (n:ℤ) + 916) (38 * (n:ℤ) + 1024) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (34 * (n:ℤ) + 916) (38 * (n:ℤ) + 1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (34 * (n:ℤ) + 916) (38 * (n:ℤ) + 1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 0 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (34 * (n:ℤ) + 916) (38 * (n:ℤ) + 1024) 0 u
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

private theorem cell_10_4 (n u : ℕ) (hu : (38 * n + 1024) ≤ u ∧ u < (53 * n + 1428)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (38 * (n:ℤ) + 1024) (53 * (n:ℤ) + 1428) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (53 * (n:ℤ) + 1428) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (53 * (n:ℤ) + 1428) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (38 * (n:ℤ) + 1024) (53 * (n:ℤ) + 1428) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (38 * (n:ℤ) + 1024) (53 * (n:ℤ) + 1428) 1 u
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

private theorem cell_10_5 (n u : ℕ) (hu : (53 * n + 1428) ≤ u ∧ u < (72 * n + 1940)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (53 * (n:ℤ) + 1428) (72 * (n:ℤ) + 1940) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 7 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (53 * (n:ℤ) + 1428) (72 * (n:ℤ) + 1940) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (53 * (n:ℤ) + 1428) (72 * (n:ℤ) + 1940) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 0 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (53 * (n:ℤ) + 1428) (72 * (n:ℤ) + 1940) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (53 * (n:ℤ) + 1428) (72 * (n:ℤ) + 1940) 1 u
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

private theorem cell_10_6 (n u : ℕ) (hu : (72 * n + 1940) ≤ u ∧ u < (76 * n + 2047)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2047) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2047) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 1 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (72 * (n:ℤ) + 1940) (76 * (n:ℤ) + 2047) 1 u
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

private theorem cell_10_7 (n u : ℕ) (hu : (76 * n + 2047) ≤ u ∧ u < (91 * n + 2452)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (76 * (n:ℤ) + 2047) (91 * (n:ℤ) + 2452) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 8 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (91 * (n:ℤ) + 2452) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (91 * (n:ℤ) + 2452) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (76 * (n:ℤ) + 2047) (91 * (n:ℤ) + 2452) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (76 * (n:ℤ) + 2047) (91 * (n:ℤ) + 2452) 2 u
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

private theorem cell_10_8 (n u : ℕ) (hu : (91 * n + 2452) ≤ u ∧ u < (104 * n + 2802)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 3 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (91 * (n:ℤ) + 2452) (104 * (n:ℤ) + 2802) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (91 * (n:ℤ) + 2452) (104 * (n:ℤ) + 2802) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (91 * (n:ℤ) + 2452) (104 * (n:ℤ) + 2802) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (91 * (n:ℤ) + 2452) (104 * (n:ℤ) + 2802) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (91 * (n:ℤ) + 2452) (104 * (n:ℤ) + 2802) 2 u
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

private theorem cell_10_9 (n u : ℕ) (hu : (104 * n + 2802) ≤ u ∧ u < (110 * n + 2963)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (104 * (n:ℤ) + 2802) (110 * (n:ℤ) + 2963) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 9 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (104 * (n:ℤ) + 2802) (110 * (n:ℤ) + 2963) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 4 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (104 * (n:ℤ) + 2802) (110 * (n:ℤ) + 2963) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (104 * (n:ℤ) + 2802) (110 * (n:ℤ) + 2963) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (104 * (n:ℤ) + 2802) (110 * (n:ℤ) + 2963) 2 u
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

private theorem cell_10_10 (n u : ℕ) (hu : (110 * n + 2963) ≤ u ∧ u < (114 * n + 3071)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (110 * (n:ℤ) + 2963) (114 * (n:ℤ) + 3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (110 * (n:ℤ) + 2963) (114 * (n:ℤ) + 3071) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (110 * (n:ℤ) + 2963) (114 * (n:ℤ) + 3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (110 * (n:ℤ) + 2963) (114 * (n:ℤ) + 3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 2 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (110 * (n:ℤ) + 2963) (114 * (n:ℤ) + 3071) 2 u
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

private theorem cell_10_11 (n u : ℕ) (hu : (114 * n + 3071) ≤ u ∧ u < (129 * n + 3475)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = -1 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (114 * (n:ℤ) + 3071) (129 * (n:ℤ) + 3475) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 10 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (129 * (n:ℤ) + 3475) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (129 * (n:ℤ) + 3475) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (114 * (n:ℤ) + 3071) (129 * (n:ℤ) + 3475) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (114 * (n:ℤ) + 3071) (129 * (n:ℤ) + 3475) 3 u
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

private theorem cell_10_12 (n u : ℕ) (hu : (129 * n + 3475) ≤ u ∧ u < (148 * n + 3987)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (129 * (n:ℤ) + 3475) (148 * (n:ℤ) + 3987) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 11 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (129 * (n:ℤ) + 3475) (148 * (n:ℤ) + 3987) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 5 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (129 * (n:ℤ) + 3475) (148 * (n:ℤ) + 3987) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (129 * (n:ℤ) + 3475) (148 * (n:ℤ) + 3987) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (129 * (n:ℤ) + 3475) (148 * (n:ℤ) + 3987) 3 u
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

private theorem cell_10_13 (n u : ℕ) (hu : (148 * n + 3987) ≤ u ∧ u < (152 * n + 4095)) :
    normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 = 0 := by
  have h0 : ((38) * (u:ℤ) + ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10))/(19 * (152 * ((n:ℤ) + 27)-8)) = 4 := by
    apply floor_on_cell (38) ((5 * (152 * ((n:ℤ) + 27)-8) + 2) * 10) (19 * (152 * ((n:ℤ) + 27)-8)) (148 * (n:ℤ) + 3987) (152 * (n:ℤ) + 4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 12 := by
    apply floor_on_cell (152 * ((152 * ((n:ℤ) + 27)-8) + 1)) (8 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3987) (152 * (n:ℤ) + 4095) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 6 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3987) (152 * (n:ℤ) + 4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19 * ((152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^2) = 1 := by
    apply floor_on_cell (19 * ((152 * ((n:ℤ) + 27)-8) + 1)) (10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^2) (148 * (n:ℤ) + 3987) (152 * (n:ℤ) + 4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) * (u:ℤ) + (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)))/(19 * (152 * ((n:ℤ) + 27)-8)^3) = 3 := by
    apply floor_on_cell (76 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (4 * 10 * ((152 * ((n:ℤ) + 27)-8)^2 + (152 * ((n:ℤ) + 27)-8) + 1)) (19 * (152 * ((n:ℤ) + 27)-8)^3) (148 * (n:ℤ) + 3987) (152 * (n:ℤ) + 4095) 3 u
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

private theorem row_count_10 (n : ℕ) :
    rowZeroCount (n + 27) 10 = 92 * n + 2480 := by
  classical
  have hval (u : ℕ) : rowValue (n + 27) 10 u =
      normalizedRow (152 * ((n:ℤ) + 27)-8) u 10 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using rowValue_normalized (n + 27) 10 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n + 27))).filter
      (fun u : ℕ => normalizedRow (152 * ((n:ℤ) + 27)-8) u 10=0) = (((((((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ)) ∪ (Finset.Ico (104 * n + 2802) (110 * n + 2963) : Finset ℕ)) ∪ (Finset.Ico (110 * n + 2963) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (129 * n + 3475) (148 * n + 3987) : Finset ℕ)) ∪ (Finset.Ico (148 * n + 3987) (152 * n + 4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n + 27)
    · have hub : u < (152 * n + 4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (15 * n + 404)
      · have hf := cell_10_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at  *
        omega
      · by_cases hc1 : u < (28 * n + 754)
        · have hf := cell_10_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at  *
          omega
        · by_cases hc2 : u < (34 * n + 916)
          · have hf := cell_10_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at  *
            omega
          · by_cases hc3 : u < (38 * n + 1024)
            · have hf := cell_10_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at  *
              omega
            · by_cases hc4 : u < (53 * n + 1428)
              · have hf := cell_10_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at  *
                omega
              · by_cases hc5 : u < (72 * n + 1940)
                · have hf := cell_10_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at  *
                  omega
                · by_cases hc6 : u < (76 * n + 2047)
                  · have hf := cell_10_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at  *
                    omega
                  · by_cases hc7 : u < (91 * n + 2452)
                    · have hf := cell_10_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at  *
                      omega
                    · by_cases hc8 : u < (104 * n + 2802)
                      · have hf := cell_10_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at  *
                        omega
                      · by_cases hc9 : u < (110 * n + 2963)
                        · have hf := cell_10_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at  *
                          omega
                        · by_cases hc10 : u < (114 * n + 3071)
                          · have hf := cell_10_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at  *
                            omega
                          · by_cases hc11 : u < (129 * n + 3475)
                            · have hf := cell_10_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at  *
                              omega
                            · by_cases hc12 : u < (148 * n + 3987)
                              · have hf := cell_10_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
                              · have hf := cell_10_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at  *
                                omega
    · dsimp [L] at  *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ)) (Finset.Ico (104 * n + 2802) (110 * n + 2963) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ)) ∪ (Finset.Ico (104 * n + 2802) (110 * n + 2963) : Finset ℕ)) (Finset.Ico (110 * n + 2963) (114 * n + 3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ)) ∪ (Finset.Ico (104 * n + 2802) (110 * n + 2963) : Finset ℕ)) ∪ (Finset.Ico (110 * n + 2963) (114 * n + 3071) : Finset ℕ)) (Finset.Ico (129 * n + 3475) (148 * n + 3987) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0 * n + 0) (15 * n + 404) : Finset ℕ) ∪ (Finset.Ico (28 * n + 754) (34 * n + 916) : Finset ℕ)) ∪ (Finset.Ico (34 * n + 916) (38 * n + 1024) : Finset ℕ)) ∪ (Finset.Ico (53 * n + 1428) (72 * n + 1940) : Finset ℕ)) ∪ (Finset.Ico (76 * n + 2047) (91 * n + 2452) : Finset ℕ)) ∪ (Finset.Ico (104 * n + 2802) (110 * n + 2963) : Finset ℕ)) ∪ (Finset.Ico (110 * n + 2963) (114 * n + 3071) : Finset ℕ)) ∪ (Finset.Ico (129 * n + 3475) (148 * n + 3987) : Finset ℕ)) (Finset.Ico (148 * n + 3987) (152 * n + 4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
