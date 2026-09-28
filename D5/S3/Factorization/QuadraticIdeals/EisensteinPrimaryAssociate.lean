/- GID: D5/S3/Factorization/QuadraticIdeals/EisensteinPrimaryAssociate
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/EisensteinPrimaryAssociate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An Eisenstein element of norm one modulo three has a primary associate. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

/-- If the norm of an Eisenstein integer is one modulo three, a norm-one unit
makes it primary. The six residue classes of norm one modulo three are exactly
the reductions of the six Eisenstein units. -/
theorem exists_primary_associate (z : EisensteinOrder)
    (hz : ((QuadraticAlgebra.norm z : ℤ) : ZMod 3) = 1) :
    ∃ u : EisensteinOrder, IsUnit u ∧ QuadraticAlgebra.norm u = 1 ∧
      (3 : EisensteinOrder) ∣ u * z - 1 := by
  let a : ZMod 3 := z.re
  let b : ZMod 3 := z.im
  have hnorm : a * a - a * b + b * b = 1 := by
    calc
      a * a - a * b + b * b = ((QuadraticAlgebra.norm z : ℤ) : ZMod 3) := by
        simp [a, b, QuadraticAlgebra.norm_def]
        ring
      _ = 1 := hz
  have hcases (v : ZMod 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have finish (u : EisensteinOrder) (hu : QuadraticAlgebra.norm u = 1)
      (hr : (((u * z - 1).re : ℤ) : ZMod 3) = 0)
      (hi : (((u * z - 1).im : ℤ) : ZMod 3) = 0) :
      ∃ v : EisensteinOrder, IsUnit v ∧ QuadraticAlgebra.norm v = 1 ∧
        (3 : EisensteinOrder) ∣ v * z - 1 := by
    have huUnit : IsUnit u :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by
        simpa only [hu] using (isUnit_one : IsUnit (1 : ℤ)))
    refine ⟨u, huUnit, hu, ?_⟩
    apply (QuadraticAlgebra.algebraMap_dvd_iff).2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi⟩
  have hthreeNe : (3 : ZMod 3) ≠ 1 := by
    change (((3 : ℕ) : ZMod 3) ≠ 1)
    rw [ZMod.natCast_self]
    exact zero_ne_one
  rcases hcases a with ha | ha | ha <;> rcases hcases b with hb | hb | hb
  · norm_num [ha, hb] at hnorm
  · refine finish ⟨-1, -1⟩ (by norm_num [QuadraticAlgebra.norm_def]) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
  · refine finish ⟨1, 1⟩ (by norm_num [QuadraticAlgebra.norm_def]) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb] <;> decide
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
  · refine finish 1 (by simp) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
  · refine finish ⟨0, -1⟩ (by norm_num [QuadraticAlgebra.norm_def]) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
  · have h : (3 : ZMod 3) = 1 := by
      calc
        (3 : ZMod 3) = (1 : ZMod 3) * 1 - 1 * 2 + 2 * 2 := by ring
        _ = 1 := by simpa only [ha, hb] using hnorm
    exact (hthreeNe h).elim
  · refine finish (-1) (by simp) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb] <;> decide
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]
  · have h : (3 : ZMod 3) = 1 := by
      calc
        (3 : ZMod 3) = (2 : ZMod 3) * 2 - 2 * 1 + 1 * 1 := by ring
        _ = 1 := by simpa only [ha, hb] using hnorm
    exact (hthreeNe h).elim
  · refine finish ⟨0, 1⟩ (by norm_num [QuadraticAlgebra.norm_def]) ?_ ?_
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb] <;> decide
    · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, a, b, ha, hb]

#print axioms exists_primary_associate

end D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
