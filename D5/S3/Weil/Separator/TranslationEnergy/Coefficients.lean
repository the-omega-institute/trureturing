/- GID: D5/S3/Weil/Separator/TranslationEnergy/Coefficients
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Coefficients
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Certify rational coefficient syntax for translated-energy cells. -/

import D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace D5.S3.Weil.Separator.TranslationEnergy

open Polynomial
open D5.S0.Certificates.BoxCover.RationalIntervalExpression

noncomputable def polynomialOfExpr : Expr 1 → Option Rat[X]
  | .input _ _ _ => some X
  | .const q _ _ => some (C q)
  | .add _ _ e f => do pure ((← polynomialOfExpr e) + (← polynomialOfExpr f))
  | .neg _ _ e => do pure (-(← polynomialOfExpr e))
  | .mul _ _ e f => do pure ((← polynomialOfExpr e) * (← polynomialOfExpr f))
  | .square _ _ e => do pure ((← polynomialOfExpr e) ^ 2)
  | .inv _ _ _ => none

noncomputable def evenizedPolynomial (p : Rat[X]) : Rat[X] :=
  C (1 / 2) * (p + p.comp (-X))

/-- Ascending coefficients; trailing zeros are permitted. -/
noncomputable def coefficientPolynomial : List Rat → Rat[X]
  | [] => 0
  | a :: as => C a + X * coefficientPolynomial as

def coefficientAdd : List Rat → List Rat → List Rat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: coefficientAdd as bs

def coefficientMul : List Rat → List Rat → List Rat
  | [], _ => []
  | a :: as, bs => if as = [] then bs.map (a * ·)
      else coefficientAdd (bs.map (a * ·)) (0 :: coefficientMul as bs)

def coefficientNegArgument : List Rat → List Rat
  | [] => []
  | a :: as => a :: (coefficientNegArgument as).map (-·)

def evenizedCoefficients (as : List Rat) : List Rat :=
  (coefficientAdd as (coefficientNegArgument as)).map ((1 / 2 : Rat) * ·)

def coefficientsOfExpr : Expr 1 → Option (List Rat)
  | .input _ _ _ => some [0, 1]
  | .const q _ _ => some [q]
  | .add _ _ e f => do pure (coefficientAdd (← coefficientsOfExpr e) (← coefficientsOfExpr f))
  | .neg _ _ e => do pure ((← coefficientsOfExpr e).map (-·))
  | .mul _ _ e f => do pure (coefficientMul (← coefficientsOfExpr e) (← coefficientsOfExpr f))
  | .square _ _ e => do
      let as ← coefficientsOfExpr e
      pure (coefficientMul as as)
  | .inv _ _ _ => none

private theorem coefficient_add_sound (as bs : List Rat) :
    coefficientPolynomial (coefficientAdd as bs) =
      coefficientPolynomial as + coefficientPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [coefficientAdd, coefficientPolynomial]
  | cons a as ih =>
      cases bs with
      | nil => simp [coefficientAdd, coefficientPolynomial]
      | cons b bs => simp [coefficientAdd, coefficientPolynomial, ih]; ring

private theorem coefficient_scale_sound (c : Rat) (as : List Rat) :
    coefficientPolynomial (as.map (c * ·)) = C c * coefficientPolynomial as := by
  induction as with
  | nil => simp [coefficientPolynomial]
  | cons a as ih => simp [coefficientPolynomial, ih]; ring

private theorem coefficient_neg_sound (as : List Rat) :
    coefficientPolynomial (as.map (-·)) = -coefficientPolynomial as := by
  induction as with
  | nil => simp [coefficientPolynomial]
  | cons a as ih => simp [coefficientPolynomial, ih]; ring

private theorem coefficient_mul_sound (as bs : List Rat) :
    coefficientPolynomial (coefficientMul as bs) =
      coefficientPolynomial as * coefficientPolynomial bs := by
  induction as with
  | nil => simp [coefficientMul, coefficientPolynomial]
  | cons a as ih =>
      by_cases h : as = []
      · subst as
        simp [coefficientMul, coefficient_scale_sound, coefficientPolynomial]
      · simp [coefficientMul, h, coefficient_add_sound, coefficient_scale_sound,
          coefficientPolynomial, ih]
        ring

private theorem coefficient_negArgument_sound (as : List Rat) :
    coefficientPolynomial (coefficientNegArgument as) =
      (coefficientPolynomial as).comp (-X) := by
  induction as with
  | nil => simp [coefficientNegArgument, coefficientPolynomial]
  | cons a as ih =>
      simp [coefficientNegArgument, coefficientPolynomial, coefficient_neg_sound, ih]

theorem evenized_coefficients_sound (as : List Rat) :
    coefficientPolynomial (evenizedCoefficients as) =
      evenizedPolynomial (coefficientPolynomial as) := by
  simp [evenizedCoefficients, coefficient_scale_sound, coefficient_add_sound,
    coefficient_negArgument_sound, evenizedPolynomial]

/-- The computational inputs do not restrict the rational-polynomial quantifiers. -/
theorem coefficientPolynomial_surjective : Function.Surjective coefficientPolynomial := by
  intro p
  induction p using Polynomial.induction_on with
  | C a => exact ⟨[a], by simp [coefficientPolynomial]⟩
  | add p q hp hq =>
      obtain ⟨as, rfl⟩ := hp
      obtain ⟨bs, rfl⟩ := hq
      exact ⟨coefficientAdd as bs, coefficient_add_sound as bs⟩
  | monomial n a ih =>
      obtain ⟨as, has⟩ := ih
      refine ⟨0 :: as, ?_⟩
      simp only [coefficientPolynomial, C_0, zero_add, has, pow_succ]
      ring

theorem coefficientsOfExpr_sound (e : Expr 1) (as : List Rat)
    (h : coefficientsOfExpr e = some as) :
    polynomialOfExpr e = some (coefficientPolynomial as) := by
  induction e generalizing as with
  | input i l u => simp [coefficientsOfExpr] at h; subst as; simp [polynomialOfExpr, coefficientPolynomial]
  | const c l u => simp [coefficientsOfExpr] at h; subst as; simp [polynomialOfExpr, coefficientPolynomial]
  | add l u e f ihe ihf =>
      cases he : coefficientsOfExpr e <;> cases hf : coefficientsOfExpr f <;>
        simp [coefficientsOfExpr, he, hf] at h
      subst as
      simp [polynomialOfExpr, ihe _ he, ihf _ hf, coefficient_add_sound]
  | neg l u e ihe =>
      cases he : coefficientsOfExpr e <;> simp [coefficientsOfExpr, he] at h
      subst as
      simp [polynomialOfExpr, ihe _ he, coefficient_neg_sound]
  | mul l u e f ihe ihf =>
      cases he : coefficientsOfExpr e <;> cases hf : coefficientsOfExpr f <;>
        simp [coefficientsOfExpr, he, hf] at h
      subst as
      simp [polynomialOfExpr, ihe _ he, ihf _ hf, coefficient_mul_sound]
  | square l u e ihe =>
      cases he : coefficientsOfExpr e <;> simp [coefficientsOfExpr, he] at h
      subst as
      simp [polynomialOfExpr, ihe _ he, coefficient_mul_sound, pow_two]
  | inv l u e ihe => simp [coefficientsOfExpr] at h


end D5.S3.Weil.Separator.TranslationEnergy
