/- GID: D5/S3/Weil/Separator/TranslationEnergy/Cell
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Cell
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Check and enclose a canonical translated-energy cell. -/

import D5.S3.Weil.Separator.TranslationEnergy.Source
import D5.S3.Weil.Separator.TranslationEnergy.Coefficients
import D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace D5.S3.Weil.Separator.TranslationEnergy

open Polynomial
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.TestFunctions
open Set MeasureTheory

def absLower (a b : Rat) : Rat :=
  if 0 ≤ a then a else if b ≤ 0 then -b else 0

def absUpper (a b : Rat) : Rat := max |a| |b|

def cutoffArgLower (R : Nat) (a b : Rat) : Rat := 2 - absUpper a b / R

def cutoffArgUpper (R : Nat) (a b : Rat) : Rat := 2 - absLower a b / R

def cutoffCellBox (R : Nat) (a b : Rat) (m n : Nat) : Rat × Rat :=
  ((cutoffLogisticInterval (cutoffArgLower R a b) m n).1,
   (cutoffLogisticInterval (cutoffArgUpper R a b) m n).2)


structure NormSqBounds where
  reHere : Rat × Rat
  reShift : Rat × Rat
  reDiff : Rat × Rat
  reSquare : Rat × Rat
  imHere : Rat × Rat
  imShift : Rat × Rat
  imDiff : Rat × Rat
  imSquare : Rat × Rat
  total : Rat × Rat

structure CanonicalCellPayload where
  pHere : Expr 1
  qHere : Expr 1
  pShift : Expr 1
  qShift : Expr 1
  norm : NormSqBounds

def singleBox (a b : Rat) (_ : Fin 1) : Rat × Rat := (a, b)

def cellInputBox (R : Nat) (a b s : Rat) (m n : Nat)
    (payload : CanonicalCellPayload) (j : Fin 6) : Rat × Rat :=
  ![cutoffCellBox R a b m n, cutoffCellBox R (a - s) (b - s) m n,
    bounds payload.pHere, bounds payload.qHere,
    bounds payload.pShift, bounds payload.qShift] j

def cellNormSqExpr (R : Nat) (a b s : Rat) (m n : Nat)
    (payload : CanonicalCellPayload) : Expr 6 :=
  let x (i : Fin 6) := Expr.input i
    (cellInputBox R a b s m n payload i).1 (cellInputBox R a b s m n payload i).2
  let w := x 0
  let ws := x 1
  let ph := x 2
  let qh := x 3
  let ps := x 4
  let qs := x 5
  let rh := Expr.mul payload.norm.reHere.1 payload.norm.reHere.2 w ph
  let rs := Expr.mul payload.norm.reShift.1 payload.norm.reShift.2 ws ps
  let rd := Expr.add payload.norm.reDiff.1 payload.norm.reDiff.2 rh
    (.neg (-payload.norm.reShift.2) (-payload.norm.reShift.1) rs)
  let ih := Expr.mul payload.norm.imHere.1 payload.norm.imHere.2 w qh
  let is := Expr.mul payload.norm.imShift.1 payload.norm.imShift.2 ws qs
  let id := Expr.add payload.norm.imDiff.1 payload.norm.imDiff.2 ih
    (.neg (-payload.norm.imShift.2) (-payload.norm.imShift.1) is)
  let r2 := Expr.square payload.norm.reSquare.1 payload.norm.reSquare.2 rd
  let i2 := Expr.square payload.norm.imSquare.1 payload.norm.imSquare.2 id
  .add payload.norm.total.1 payload.norm.total.2 r2 i2

def canonicalCellAccepted (R : Nat) (p q : List Rat) (s : Rat)
    (meshDepth i cutoffWidthDepth taylorDepth : Nat)
    (payload : CanonicalCellPayload) : Prop :=
  match cellAt R s meshDepth i with
  | none => False
  | some (a, b) =>
      0 < R ∧ a ≤ b ∧
      checkCutoffLogistic (cutoffArgLower R a b) cutoffWidthDepth taylorDepth = true ∧
      checkCutoffLogistic (cutoffArgUpper R a b) cutoffWidthDepth taylorDepth = true ∧
      checkCutoffLogistic (cutoffArgLower R (a - s) (b - s))
        cutoffWidthDepth taylorDepth = true ∧
      checkCutoffLogistic (cutoffArgUpper R (a - s) (b - s))
        cutoffWidthDepth taylorDepth = true ∧
      coefficientsOfExpr payload.pHere = some (evenizedCoefficients p) ∧
      coefficientsOfExpr payload.qHere = some (evenizedCoefficients q) ∧
      coefficientsOfExpr payload.pShift = some (evenizedCoefficients p) ∧
      coefficientsOfExpr payload.qShift = some (evenizedCoefficients q) ∧
      check (singleBox a b) payload.pHere = true ∧
      check (singleBox a b) payload.qHere = true ∧
      check (singleBox (a - s) (b - s)) payload.pShift = true ∧
      check (singleBox (a - s) (b - s)) payload.qShift = true ∧
      check (cellInputBox R a b s cutoffWidthDepth taylorDepth payload)
        (cellNormSqExpr R a b s cutoffWidthDepth taylorDepth payload) = true

instance canonicalCellAcceptedDecidable (R : Nat) (p q : List Rat) (s : Rat)
    (meshDepth i cutoffWidthDepth taylorDepth : Nat)
    (payload : CanonicalCellPayload) :
    Decidable (canonicalCellAccepted R p q s meshDepth i cutoffWidthDepth
      taylorDepth payload) := by
  unfold canonicalCellAccepted
  split <;> infer_instance

def checkCanonicalCell (R : Nat) (p q : List Rat) (s : Rat)
    (meshDepth i cutoffWidthDepth taylorDepth : Nat)
    (payload : CanonicalCellPayload) : Bool :=
  decide (canonicalCellAccepted R p q s meshDepth i cutoffWidthDepth
    taylorDepth payload)

private theorem cutoff_cell_box_sound (R : Nat) (hR : 0 < R) (a b : Rat)
    (m n : Nat) (hl : checkCutoffLogistic (cutoffArgLower R a b) m n = true)
    (hu : checkCutoffLogistic (cutoffArgUpper R a b) m n = true)
    (y : Real) (hy : (a : Real) ≤ y ∧ y ≤ (b : Real)) :
    ((cutoffCellBox R a b m n).1 : Real) ≤
        Real.smoothTransition (2 - |y| / R) ∧
      Real.smoothTransition (2 - |y| / R) ≤
        ((cutoffCellBox R a b m n).2 : Real) := by
  have hr : (0 : Real) < R := by exact_mod_cast hR
  have habs : (absLower a b : Real) ≤ |y| ∧ |y| ≤ (absUpper a b : Real) := by
    constructor
    · simp only [absLower]
      split_ifs with ha hb
      · rw [abs_of_nonneg ((show (0 : Real) ≤ (a : Real) by exact_mod_cast ha).trans hy.1)]
        exact hy.1
      · rw [abs_of_nonpos (hy.2.trans (show (b : Real) ≤ 0 by exact_mod_cast hb))]
        simpa only [Rat.cast_neg] using neg_le_neg hy.2
      · simpa only [Rat.cast_zero] using abs_nonneg y
    · by_cases hy0 : 0 ≤ y
      · rw [abs_of_nonneg hy0]
        exact hy.2.trans ((le_abs_self (b : Real)).trans (by
          exact_mod_cast (le_max_right |a| |b|)))
      · rw [abs_of_nonpos (le_of_not_ge hy0)]
        exact (neg_le_neg hy.1).trans ((neg_le_abs (a : Real)).trans (by
          exact_mod_cast (le_max_left |a| |b|)))
  have ht : (cutoffArgLower R a b : Real) ≤ 2 - |y| / R ∧
      2 - |y| / R ≤ (cutoffArgUpper R a b : Real) := by
    dsimp [cutoffArgLower, cutoffArgUpper]
    push_cast
    constructor <;> apply sub_le_sub_left
    · exact div_le_div_of_nonneg_right habs.2 hr.le
    · exact div_le_div_of_nonneg_right habs.1 hr.le
  have hlow := checked_cutoff_logistic_sound (cutoffArgLower R a b) m n hl
  have hupp := checked_cutoff_logistic_sound (cutoffArgUpper R a b) m n hu
  exact ⟨hlow.2.1.trans (Real.smoothTransition.monotone ht.1),
    (Real.smoothTransition.monotone ht.2).trans hupp.2.2.1⟩

private theorem value_eq_aeval_of_polynomialOfExpr (e : Expr 1) (r : Rat[X])
    (y : Real) (h : polynomialOfExpr e = some r) :
    value (fun _ => y) e = aeval y r := by
  induction e generalizing r with
  | input i l u =>
      simp only [polynomialOfExpr, Option.some.injEq] at h
      subst r
      simp [value]
  | const c l u =>
      simp only [polynomialOfExpr, Option.some.injEq] at h
      subst r
      simp [value]
  | add l u e f ihe ihf =>
      cases he : polynomialOfExpr e with
      | none => simp [polynomialOfExpr, he] at h
      | some re =>
          cases hf : polynomialOfExpr f with
          | none => simp [polynomialOfExpr, he, hf] at h
          | some rf =>
              simp [polynomialOfExpr, he, hf] at h
              subst r
              simp [value, ihe _ he, ihf _ hf]
  | neg l u e ihe =>
      cases he : polynomialOfExpr e with
      | none => simp [polynomialOfExpr, he] at h
      | some re =>
          simp [polynomialOfExpr, he] at h
          subst r
          simp [value, ihe _ he]
  | mul l u e f ihe ihf =>
      cases he : polynomialOfExpr e with
      | none => simp [polynomialOfExpr, he] at h
      | some re =>
          cases hf : polynomialOfExpr f with
          | none => simp [polynomialOfExpr, he, hf] at h
          | some rf =>
              simp [polynomialOfExpr, he, hf] at h
              subst r
              simp [value, ihe _ he, ihf _ hf]
  | square l u e ihe =>
      cases he : polynomialOfExpr e with
      | none => simp [polynomialOfExpr, he] at h
      | some re =>
          simp [polynomialOfExpr, he] at h
          subst r
          simp [value, ihe _ he]
  | inv l u e ihe => simp [polynomialOfExpr] at h

theorem checked_canonical_cell_normSq_encloses
    (R : Nat) (p q : Rat[X]) (s : Rat)
    (pCoefficients qCoefficients : List Rat)
    (hpCoefficients : coefficientPolynomial pCoefficients = p)
    (hqCoefficients : coefficientPolynomial qCoefficients = q)
    (meshDepth i cutoffWidthDepth taylorDepth : Nat)
    (payload : CanonicalCellPayload) (a b : Rat)
    (hcell : cellAt R s meshDepth i = some (a, b))
    (hcheck : checkCanonicalCell R pCoefficients qCoefficients s meshDepth i cutoffWidthDepth
      taylorDepth payload = true)
    (y : Real) (hy : (a : Real) ≤ y ∧ y ≤ (b : Real)) :
    let H : Real → Complex := fun x =>
      ((Real.smoothTransition (2 - |x| / R) : Real) : Complex) *
        rationalEvenPolynomial p q x
    ((bounds (cellNormSqExpr R a b s cutoffWidthDepth taylorDepth payload)).1 : Real) ≤
        Complex.normSq (H y - H (y - s)) ∧
      Complex.normSq (H y - H (y - s)) ≤
        ((bounds (cellNormSqExpr R a b s cutoffWidthDepth taylorDepth payload)).2 : Real) := by
  dsimp only
  have ha := of_decide_eq_true hcheck
  simp only [canonicalCellAccepted, hcell] at ha
  rcases ha with ⟨hR, hab, hcl, hcu, hcsl, hcsu, hp, hq, hps, hqs,
    hpCheck, hqCheck, hpsCheck, hqsCheck, hfinal⟩
  have hp := coefficientsOfExpr_sound _ _ hp
  have hq := coefficientsOfExpr_sound _ _ hq
  have hps := coefficientsOfExpr_sound _ _ hps
  have hqs := coefficientsOfExpr_sound _ _ hqs
  simp only [evenized_coefficients_sound, hpCoefficients, hqCoefficients] at hp hq hps hqs
  have hcut := cutoff_cell_box_sound R hR a b cutoffWidthDepth taylorDepth
    hcl hcu y hy
  have hyShift : ((a - s : Rat) : Real) ≤ y - s ∧ y - s ≤ ((b - s : Rat) : Real) := by
    push_cast
    exact ⟨sub_le_sub_right hy.1 (s : Real), sub_le_sub_right hy.2 (s : Real)⟩
  have hcutShift := cutoff_cell_box_sound R hR (a - s) (b - s)
    cutoffWidthDepth taylorDepth hcsl hcsu (y - s) hyShift
  have polyBounds (e : Expr 1) (r : Rat[X]) (u v : Rat) (x : Real)
      (hx : (u : Real) ≤ x ∧ x ≤ (v : Real))
      (he : polynomialOfExpr e = some (evenizedPolynomial r))
      (hc : check (singleBox u v) e = true) :
      ((bounds e).1 : Real) ≤ ((aeval x r : Real) + aeval (-x) r) / 2 ∧
        ((aeval x r : Real) + aeval (-x) r) / 2 ≤ ((bounds e).2 : Real) := by
    have hh := checked_expression_encloses (singleBox u v) (fun _ => x)
      (fun _ => hx) e hc
    rw [value_eq_aeval_of_polynomialOfExpr e (evenizedPolynomial r) x he] at hh
    simpa [evenizedPolynomial, Polynomial.aeval_comp, div_eq_mul_inv, mul_comm] using hh
  have hph := polyBounds payload.pHere p a b y hy hp hpCheck
  have hqh := polyBounds payload.qHere q a b y hy hq hqCheck
  have hps' := polyBounds payload.pShift p (a - s) (b - s) (y - s)
    hyShift hps hpsCheck
  have hqs' := polyBounds payload.qShift q (a - s) (b - s) (y - s)
    hyShift hqs hqsCheck
  let vals : Fin 6 → Real := ![
    Real.smoothTransition (2 - |y| / R),
    Real.smoothTransition (2 - |y - s| / R),
    ((aeval y p : Real) + aeval (-y) p) / 2,
    ((aeval y q : Real) + aeval (-y) q) / 2,
    ((aeval (y - s) p : Real) + aeval (-(y - s)) p) / 2,
    ((aeval (y - s) q : Real) + aeval (-(y - s)) q) / 2]
  have hv : ∀ j, ((cellInputBox R a b s cutoffWidthDepth taylorDepth payload j).1 : Real) ≤ vals j ∧
      vals j ≤ ((cellInputBox R a b s cutoffWidthDepth taylorDepth payload j).2 : Real) := by
    intro j
    fin_cases j <;> simp [cellInputBox, vals]
    · exact hcut
    · exact hcutShift
    · exact hph
    · exact hqh
    · simpa only [neg_sub] using hps'
    · simpa only [neg_sub] using hqs'
  have hout := checked_expression_encloses
    (cellInputBox R a b s cutoffWidthDepth taylorDepth payload) vals hv
    (cellNormSqExpr R a b s cutoffWidthDepth taylorDepth payload) hfinal
  have hvalue : value vals (cellNormSqExpr R a b s cutoffWidthDepth taylorDepth payload) =
      Complex.normSq
        ((((Real.smoothTransition (2 - |y| / R) : Real) : Complex) *
            rationalEvenPolynomial p q y) -
          ((Real.smoothTransition (2 - |y - s| / R) : Real) : Complex) *
            rationalEvenPolynomial p q (y - s)) := by
    simp [cellNormSqExpr, cellInputBox, value, vals, rationalEvenPolynomial,
      Complex.normSq_apply]
    ring
  simpa only [hvalue, Rat.cast_sub] using hout

/-- A total list lookup uses this value only outside the checked index range. -/
def defaultPayload : CanonicalCellPayload where
  pHere := .const 0 0 0
  qHere := .const 0 0 0
  pShift := .const 0 0 0
  qShift := .const 0 0 0
  norm := {
    reHere := (0, 0), reShift := (0, 0), reDiff := (0, 0), reSquare := (0, 0),
    imHere := (0, 0), imShift := (0, 0), imDiff := (0, 0), imSquare := (0, 0),
    total := (0, 0) }


end D5.S3.Weil.Separator.TranslationEnergy
