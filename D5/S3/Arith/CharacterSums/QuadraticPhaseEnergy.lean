/- GID: D5/S3/Arith/CharacterSums/QuadraticPhaseEnergy
   generality: G
   mirror-B: none(waiver:finite-field-character-energy-infrastructure)
   mirror-E: none(waiver:finite-field-character-energy-infrastructure)
   anchors: []
   utility: none
   digest: Product of opposite quadratic additive-character phases equals the field cardinality. -/

module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Quadratic additive-character phase energy

For an odd finite field and a nontrivial complex additive character, the product of a
quadratic phase sum and its opposite phase sum is the cardinality of the field.  The
proof is a translation of the double sum followed by additive-character orthogonality.
-/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums

set_option autoImplicit false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Opposite quadratic additive-character phases have energy equal to the field size. -/
theorem quadratic_phase_energy
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (d e : F) (hd : d ≠ 0) :
    (∑ x : F, ψ (d * x ^ 2 + e * x)) *
      (∑ y : F, ψ (-(d * y ^ 2 + e * y))) = (Fintype.card F : ℂ) := by
  classical
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hprim : AddChar.IsPrimitive ψ := AddChar.IsPrimitive.of_ne_one hψ
  calc
    _ = ∑ x : F, ∑ y : F,
        ψ ((d * x ^ 2 + e * x) - (d * y ^ 2 + e * y)) := by
      simp only [Fintype.sum_mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul]
    _ = ∑ h : F, ∑ y : F,
        ψ ((2 * d * h) * y + (d * h ^ 2 + e * h)) := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ y : F, ∑ h : F,
            ψ ((2 * d * h) * y + (d * h ^ 2 + e * h)) := by
          apply Finset.sum_congr rfl
          intro y _
          symm
          apply Fintype.sum_equiv (Equiv.addRight y)
          intro h
          congr 1
          change (2 * d * h) * y + (d * h ^ 2 + e * h) =
            (d * (h + y) ^ 2 + e * (h + y)) - (d * y ^ 2 + e * y)
          ring
        _ = _ := Finset.sum_comm
    _ = ∑ h : F,
        (∑ y : F, ψ ((2 * d * h) * y)) *
          ψ (d * h ^ 2 + e * h) := by
      simp only [AddChar.map_add_eq_mul, Finset.sum_mul]
    _ = _ := by
      have hsum (h : F) :
          (∑ y : F, ψ ((2 * d * h) * y)) =
            if (2 * d * h) = 0 then (Fintype.card F : ℂ) else 0 := by
        rw [show (∑ y : F, ψ ((2 * d * h) * y)) =
            ∑ y : F, ψ (y * (2 * d * h)) by
              apply Finset.sum_congr rfl
              intro y _
              congr 1
              ring]
        split_ifs with hh
        · simpa [hh] using (AddChar.sum_mulShift (2 * d * h) hprim)
        · simpa [hh] using (AddChar.sum_mulShift (2 * d * h) hprim)
      simp_rw [hsum]
      simp [mul_eq_zero, htwo, hd]

end D5.S3.Arith.CharacterSums
