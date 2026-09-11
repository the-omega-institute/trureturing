/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduced archive pairs identify the actual fraction quotient with the rational field. -/

import D5.S3.ConceptDynamics.SpacetimeArithmetic.RichRational
import Mathlib.Algebra.Field.TransferInstance

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.RationalQuotient

open Spacetime.ComplementCharge Spacetime.ComplementFibers RichRational

noncomputable section
variable {d : Nat}

/-- Rat stores the reduced numerator and the positive denominator, including zero as 0/1. -/
def rationalSection (d : Nat) (r : Rat) : Fraction d where
  numerator := balancedSection d r.num
  denominator := balancedSection d (r.den : Int)
  denominator_ne_zero := by
    rw [balancedSection_rightInverse d]
    exact_mod_cast r.den_pos.ne'

theorem rationalSection_rightInverse (d : Nat) :
    Function.RightInverse (rationalSection d) (readout : Fraction d → Rat) := by
  intro r
  change (balancedQ (balancedSection d r.num) : Rat) /
    (balancedQ (balancedSection d (r.den : Int)) : Rat) = r
  rw [balancedSection_rightInverse d, balancedSection_rightInverse d, Int.cast_natCast]
  exact Rat.num_div_den r

theorem rationalSection_injective (d : Nat) : Function.Injective (rationalSection d) :=
  (rationalSection_rightInverse d).injective

theorem rationalSection_zero (d : Nat) :
    rationalSection d 0 = integerEmbedding (balancedSection d 0) := rfl

theorem rationalSection_reduced (d : Nat) (r : Rat) :
    0 < balancedQ (rationalSection d r).denominator ∧
      Nat.Coprime (balancedQ (rationalSection d r).numerator).natAbs
        (balancedQ (rationalSection d r).denominator).natAbs := by
  change 0 < balancedQ (balancedSection d (r.den : Int)) ∧
    Nat.Coprime (balancedQ (balancedSection d r.num)).natAbs
      (balancedQ (balancedSection d (r.den : Int))).natAbs
  rw [balancedSection_rightInverse d, balancedSection_rightInverse d]
  exact ⟨by exact_mod_cast r.den_pos, by simpa using r.reduced⟩

/-- Uniqueness refers to the two reduced integer coordinates, not to arbitrary archives. -/
theorem reduced_coordinates_unique (r : Rat) (a b : Int)
    (hb : 0 < b) (hcoprime : Nat.Coprime a.natAbs b.natAbs)
    (hvalue : (a : Rat) / (b : Rat) = r) : a = r.num ∧ b = (r.den : Int) := by
  apply Rat.div_int_inj hb (by exact_mod_cast r.den_pos) hcoprime
    (by simpa using r.reduced)
  simpa only [Int.cast_natCast, Rat.num_div_den] using hvalue

def Rational (d : Nat) := Quotient (kernelSetoid d)

def classOf (r : Fraction d) : Rational d := Quotient.mk (kernelSetoid d) r

/-- Reuse the standard first isomorphism theorem with the actual archive-pair section. -/
def rational_quotient_equiv (d : Nat) : Rational d ≃ Rat :=
  Setoid.quotientKerEquivOfRightInverse RichRational.readout (rationalSection d)
    (rationalSection_rightInverse d)

theorem quotient_readout (r : Fraction d) :
    rational_quotient_equiv d (classOf r) = readout r := rfl

theorem class_eq_iff (r s : Fraction d) : classOf r = classOf s ↔ CrossEquivalent r s :=
  ((rational_quotient_equiv d).injective.eq_iff.symm).trans (cross_iff_readout r s).symm

instance quotientField (d : Nat) : Field (Rational d) := (rational_quotient_equiv d).field

def rational_field_equiv (d : Nat) : Rational d ≃+* Rat :=
  Equiv.ringEquiv (rational_quotient_equiv d)

theorem class_add (r s : Fraction d) : classOf (add r s) = classOf r + classOf s := by
  apply (rational_field_equiv d).injective
  rw [map_add]
  exact add_readout r s

theorem class_mul (r s : Fraction d) : classOf (mul r s) = classOf r * classOf s := by
  apply (rational_field_equiv d).injective
  rw [map_mul]
  exact mul_readout r s

theorem class_neg (r : Fraction d) : classOf (neg r) = -classOf r := by
  apply (rational_field_equiv d).injective
  rw [map_neg]
  exact neg_readout r

/-- The field convention at zero does not remove the rich inverse's guard. -/
theorem class_inv (r : Fraction d) (h : InverseGuard r) :
    classOf (inv r h) = (classOf r)⁻¹ := by
  apply (rational_field_equiv d).injective
  rw [map_inv₀]
  exact inv_readout r h

theorem class_div (r s : Fraction d) (h : DivisionGuard s) :
    classOf (div r s h) = classOf r / classOf s := by
  apply (rational_field_equiv d).injective
  rw [map_div₀]
  exact div_readout r s h

theorem quotient_inverse_domain (r : Fraction d) :
    InverseGuard r ↔ classOf r ≠ 0 := by
  rw [inverse_guard_iff, ← map_ne_zero_iff (rational_field_equiv d)
    (rational_field_equiv d).injective]
  rfl

theorem quotient_division_domain (s : Fraction d) :
    DivisionGuard s ↔ classOf s ≠ 0 := quotient_inverse_domain s

end
end D5.S3.ConceptDynamics.SpacetimeArithmetic.RationalQuotient
