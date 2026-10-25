import D5.S3.Geometry.Hyperideal.SL2F5Involution
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false

open scoped MatrixGroups

namespace CFMPSL2F5ProjectiveInvolutionLiftsExactCheck

local notation "G" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)
local notation "P" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)
local notation "q" => (QuotientGroup.mk' (Subgroup.center G) : G →* P)

example (Y : G) (hprojective_square : (q Y) ^ 2 = 1)
    (hprojective_nontrivial : q Y ≠ 1) :
    Y ^ 2 = -1 ∧ Y ^ 4 = 1 ∧ orderOf Y = 4 := by
  have hcenter : Y ^ 2 ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff (Y ^ 2)).mp
    change q (Y ^ 2) = 1
    rw [map_pow, hprojective_square]
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hr_two : r ^ 2 = 1 := by simpa using hr
  have hsquare_sign : Y ^ 2 = 1 ∨ Y ^ 2 = -1 := by
    rcases sq_eq_one_iff.mp hr_two with hr_one | hr_negative
    · left
      apply Subtype.ext
      simpa only [hr_one, map_one, Matrix.SpecialLinearGroup.coe_one]
        using hscalar.symm
    · right
      apply Subtype.ext
      simpa only [hr_negative, map_neg, map_one,
        Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
        using hscalar.symm
  have hnegative_center : (-1 : G) ∈ Subgroup.center G := by
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨(-1 : ZMod 5), ?_, ?_⟩
    · norm_num
    · simp only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one]
  have hnegative_projective : q (-1 : G) = 1 :=
    (QuotientGroup.eq_one_iff (-1 : G)).mpr hnegative_center
  have hsquare_not_one : Y ^ 2 ≠ 1 := by
    intro hsquare
    rcases D5.S3.Geometry.Hyperideal.SL2F5Involution.sl2_zmod5_square_one_eq_one_or_neg_one
      Y hsquare with hY | hY
    · apply hprojective_nontrivial
      rw [hY, map_one]
    · apply hprojective_nontrivial
      rw [hY]
      exact hnegative_projective
  have hsquare_negative : Y ^ 2 = -1 := hsquare_sign.resolve_left hsquare_not_one
  have hfour : Y ^ 4 = 1 := by
    calc
      Y ^ 4 = (Y ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (-1 : G) ^ 2 := by rw [hsquare_negative]
      _ = 1 := by simp [pow_two]
  have horder : orderOf Y = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) hsquare_not_one hfour
  exact ⟨hsquare_negative, hfour, horder⟩

end CFMPSL2F5ProjectiveInvolutionLiftsExactCheck
