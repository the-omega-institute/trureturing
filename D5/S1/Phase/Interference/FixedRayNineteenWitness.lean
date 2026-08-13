/- GID: D5/S1/Phase/Interference/FixedRayNineteenWitness
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/FixedRayNineteenWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two admissible cases at modulus nineteen have unequal Jacobi selector values. -/

import D5.S1.Phase.Interference.ZolotarevSelector

namespace D5.S1.Phase.Interference.FixedRayNineteenWitness

open scoped NumberTheorySymbols

def fixedRayModulus : ℤ := 19

def fixedRayAdmissible (beta gamma0 : ℤ) : Prop :=
  4 * beta * gamma0 ≡ -1 [ZMOD fixedRayModulus]

def fixedRaySelector (beta : ℤ) : ℤ := J(beta | fixedRayModulus.natAbs)

theorem fixed_ray_case_one :
    fixedRayAdmissible 1 14 ∧ fixedRaySelector 1 = 1 := by
  constructor
  · norm_num [fixedRayAdmissible, fixedRayModulus, Int.ModEq]
  · rw [fixedRaySelector, fixedRayModulus]
    simp

theorem fixed_ray_case_two :
    fixedRayAdmissible 2 7 ∧ fixedRaySelector 2 = -1 := by
  constructor
  · norm_num [fixedRayAdmissible, fixedRayModulus, Int.ModEq]
  · rw [fixedRaySelector, fixedRayModulus]
    change J(2 | 19) = -1
    rw [jacobiSym.at_two (by decide : Odd 19), ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num

theorem fixed_ray_nineteen_witness :
    ∃ beta₁ gamma₁ beta₂ gamma₂ : ℤ,
      fixedRayAdmissible beta₁ gamma₁ ∧
        fixedRayAdmissible beta₂ gamma₂ ∧
          fixedRaySelector beta₁ ≠ fixedRaySelector beta₂ := by
  refine ⟨1, 14, 2, 7, fixed_ray_case_one.1, fixed_ray_case_two.1, ?_⟩
  rw [fixed_ray_case_one.2, fixed_ray_case_two.2]
  norm_num

theorem no_fixed_ray_character :
    ¬∃ χ : ℤ → ℤ, ∀ beta gamma0 : ℤ,
      fixedRayAdmissible beta gamma0 →
        fixedRaySelector beta = χ fixedRayModulus := by
  rintro ⟨χ, hχ⟩
  have hOne := hχ 1 14 fixed_ray_case_one.1
  have hTwo := hχ 2 7 fixed_ray_case_two.1
  have hEqual : fixedRaySelector 1 = fixedRaySelector 2 := hOne.trans hTwo.symm
  rw [fixed_ray_case_one.2, fixed_ray_case_two.2] at hEqual
  norm_num at hEqual

end D5.S1.Phase.Interference.FixedRayNineteenWitness
