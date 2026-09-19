/- GID: D5/S3/Weil/Separator/TranslationEnergy/Integral
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Integral
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Aggregate canonical cell enclosures into literal translation energy. -/

import D5.S3.Weil.Separator.TranslationEnergy.Cell
import D5.S3.Weil.Separator.TranslationEnergy.Geometry
import D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
import D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

noncomputable section

namespace D5.S3.Weil.Separator.TranslationEnergy.LiteralFunction

open Set Polynomial
open scoped ContDiff
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation

/-- The literal rational test whose cutoff is the smooth transition with
plateau radius `R` and support radius `2 * R`. -/
def literalRationalTest (R : Nat) (hR : 0 < R) (p q : Rat[X]) : WeilTestFunction where
  toFun x :=
    ((Real.smoothTransition (2 - |x| / (R : Real)) : Real) : Complex) *
      rationalEvenPolynomial p q x
  contDiff' := by
    have hRr : (0 : Real) < R := Nat.cast_pos.mpr hR
    let chi : Real -> Real := fun x => Real.smoothTransition (2 - |x| / (R : Real))
    have hchi : ContDiff Real ∞ chi := by
      rw [contDiff_iff_contDiffAt]
      intro x
      have hb := (ContDiffBumpBase.ofInnerProductSpace Real).smooth.contDiffAt
        (show Ioi (1 : Real) ×ˢ (univ : Set Real) ∈
          nhds ((2 : Real), x / (R : Real)) from
          prod_mem_nhds (Ioi_mem_nhds (by norm_num)) Filter.univ_mem)
      have ht := hb.comp x
        ((contDiffAt_const (c := (2 : Real))).prodMk
          ((contDiffAt_id (x := x)).div_const (R : Real)))
      change ContDiffAt Real ∞ (fun y : Real =>
        Real.smoothTransition (((2 : Real) - ‖y / (R : Real)‖) / (2 - 1))) x at ht
      simpa [chi, Real.norm_eq_abs, abs_div, abs_of_pos hRr,
        show (2 : Real) - 1 = 1 by norm_num] using ht
    apply (Complex.ofRealCLM.contDiff.comp hchi).mul
    have hpoly (r : Rat[X]) : ContDiff Real ∞ (fun x : Real =>
        ((aeval x r : Real) + aeval (-x) r) / 2) :=
      ((r.contDiff_aeval ∞).add
        ((r.contDiff_aeval ∞).comp contDiff_neg)).div_const 2
    exact (Complex.ofRealCLM.contDiff.comp (hpoly p)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hpoly q)))
  hasCompactSupport' := by
    have hRr : (0 : Real) < R := Nat.cast_pos.mpr hR
    let chi : Real -> Real := fun x => Real.smoothTransition (2 - |x| / (R : Real))
    let c : Real -> Complex := fun x => (chi x : Complex)
    have hcS : tsupport c ⊆ Icc (-(2 * R : Real)) (2 * R) := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      have hne : chi x ≠ 0 := by
        intro hz
        exact hx (by simp [c, hz])
      have hpos : 0 < 2 - |x| / (R : Real) := by
        by_contra hn
        exact hne (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hn))
      have hbound : |x| < 2 * (R : Real) := (div_lt_iff₀ hRr).mp (by linarith)
      exact abs_le.mp hbound.le
    have hcompact : HasCompactSupport c :=
      isCompact_Icc.of_isClosed_subset isClosed_closure hcS
    exact hcompact.mul_right
  even' := fun x => by
    simp [rationalEvenPolynomial, abs_neg, add_comm]

end D5.S3.Weil.Separator.TranslationEnergy.LiteralFunction

end

namespace D5.S3.Weil.Separator.TranslationEnergy

open Polynomial
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open Set MeasureTheory
open scoped BigOperators

def aggregateBounds (R : Nat) (s : Rat) (meshDepth : Nat)
    (payloads : List CanonicalCellPayload) : Rat × Rat :=
  (∑ i ∈ Finset.range payloads.length,
      match cellAt R s meshDepth i with
      | none => 0
      | some (a, b) => (b - a) * (payloads.getD i defaultPayload).norm.total.1,
   ∑ i ∈ Finset.range payloads.length,
      match cellAt R s meshDepth i with
      | none => 0
      | some (a, b) => (b - a) * (payloads.getD i defaultPayload).norm.total.2)

/-- Every adjacent source cell, including support gaps, must have exactly one payload. -/
def fullAccepted (R : Nat) (p q : List Rat) (s : Rat)
    (meshDepth cutoffWidthDepth taylorDepth requestedWidthDepth : Nat)
    (payloads : List CanonicalCellPayload) : Prop :=
  0 < R ∧
  payloads.length + 1 = (canonicalPoints R s meshDepth).length ∧
  (canonicalPoints R s meshDepth)[0]? = some (supportHullLower R s) ∧
  (canonicalPoints R s meshDepth)[payloads.length]? = some (supportHullUpper R s) ∧
  (List.range payloads.length).all (fun i =>
    checkCanonicalCell R p q s meshDepth i cutoffWidthDepth taylorDepth
      (payloads.getD i defaultPayload)) = true ∧
  (aggregateBounds R s meshDepth payloads).2 -
      (aggregateBounds R s meshDepth payloads).1 ≤ (1 / 2 : Rat) ^ requestedWidthDepth

instance (R : Nat) (p q : List Rat) (s : Rat) (d m n k : Nat)
    (payloads : List CanonicalCellPayload) : Decidable (fullAccepted R p q s d m n k payloads) := by
  unfold fullAccepted
  infer_instance

def checkFull (R : Nat) (p q : List Rat) (s : Rat) (d m n k : Nat)
    (payloads : List CanonicalCellPayload) : Bool :=
  decide (fullAccepted R p q s d m n k payloads)

def roundedInterval (box : Rat × Rat) : Rat × Rat :=
  (((Int.floor (box.1 * (2 ^ 32 : Rat)) : Int) : Rat) / 2 ^ 32,
   ((Int.ceil (box.2 * (2 ^ 32 : Rat)) : Int) : Rat) / 2 ^ 32)

def unitPolynomialPayload (R : Nat) (a b s : Rat) (m n : Nat) : CanonicalCellPayload :=
  let here := roundedInterval (cutoffCellBox R a b m n)
  let shifted := roundedInterval (cutoffCellBox R (a - s) (b - s) m n)
  let diff := (here.1 - shifted.2, here.2 - shifted.1)
  let sq := SignedSquares.squareBounds diff.1 diff.2
  { pHere := .const 1 1 1, qHere := .const 1 1 1,
    pShift := .const 1 1 1, qShift := .const 1 1 1,
    norm := {
      reHere := here, reShift := shifted, reDiff := diff, reSquare := sq,
      imHere := here, imShift := shifted, imDiff := diff, imSquare := sq,
      total := (2 * sq.1, 2 * sq.2) } }

def unitPolynomialPayloads (R : Nat) (s : Rat) (d m n : Nat) : List CanonicalCellPayload :=
  (sourceCells R s d).map fun (a, b) => unitPolynomialPayload R a b s m n

theorem checked_canonical_cell_integral_encloses
    (R : Nat) (p q : Rat[X]) (s : Rat) (pcs qcs : List Rat)
    (hpcs : coefficientPolynomial pcs = p) (hqcs : coefficientPolynomial qcs = q)
    (d i m n : Nat) (payload : CanonicalCellPayload) (a b : Rat)
    (hcell : cellAt R s d i = some (a, b))
    (hcheck : checkCanonicalCell R pcs qcs s d i m n payload = true)
    (f : WeilTestFunction)
    (hf : ∀ x : Real, f x =
      ((Real.smoothTransition (2 - |x| / R) : Real) : Complex) * rationalEvenPolynomial p q x) :
    (((b - a) * payload.norm.total.1 : Rat) : Real) ≤
        ∫ y in (a : Real)..(b : Real), Complex.normSq (f y - f (y - s)) ∧
      (∫ y in (a : Real)..(b : Real), Complex.normSq (f y - f (y - s))) ≤
        (((b - a) * payload.norm.total.2 : Rat) : Real) := by
  have ha := of_decide_eq_true hcheck
  simp only [canonicalCellAccepted, hcell] at ha
  have hab : (a : Real) ≤ (b : Real) := by exact_mod_cast ha.2.1
  have hc : Continuous (fun y : Real => Complex.normSq (f y - f (y - s))) :=
    Complex.continuous_normSq.comp
      (f.continuous.sub (f.continuous.comp (continuous_id.sub continuous_const)))
  have hi : IntervalIntegrable (fun y : Real => Complex.normSq (f y - f (y - s)))
      volume (a : Real) (b : Real) := hc.intervalIntegrable _ _
  have hpoint (y : Real) (hy : y ∈ Icc (a : Real) (b : Real)) :=
    checked_canonical_cell_normSq_encloses R p q s pcs qcs hpcs hqcs d i m n
      payload a b hcell hcheck y hy
  have hl := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := (payload.norm.total.1 : Real))) hi
    (fun y hy => by simpa only [hf, bounds, cellNormSqExpr] using (hpoint y hy).1)
  have hu := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (payload.norm.total.2 : Real)))
    (fun y hy => by simpa only [hf, bounds, cellNormSqExpr] using (hpoint y hy).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, Rat.cast_mul,
    Rat.cast_sub] using And.intro hl hu

theorem checked_literal_translation_energy_sound
    (R : Nat) (p q : Rat[X]) (s : Rat) (pcs qcs : List Rat)
    (hpcs : coefficientPolynomial pcs = p) (hqcs : coefficientPolynomial qcs = q)
    (d m n k : Nat) (payloads : List CanonicalCellPayload)
    (hcheck : checkFull R pcs qcs s d m n k payloads = true)
    (f : WeilTestFunction)
    (hf : ∀ x : Real, f x =
      ((Real.smoothTransition (2 - |x| / R) : Real) : Complex) * rationalEvenPolynomial p q x) :
    let box := aggregateBounds R s d payloads
    (box.1 : Real) ≤ translationEnergy f s ∧
      translationEnergy f s ≤ (box.2 : Real) ∧
      box.2 - box.1 ≤ (1 / 2 : Rat) ^ k := by
  dsimp only
  have ha := of_decide_eq_true hcheck
  rcases ha with ⟨hR, hlen, hfirst, hlast, hchecks, hwidth⟩
  have hchecks : ∀ i, i < payloads.length →
      checkCanonicalCell R pcs qcs s d i m n (payloads.getD i defaultPayload) = true := by
    simpa only [List.all_eq_true, List.mem_range] using hchecks
  let x : Nat → Rat := fun i => (canonicalPoints R s d).getD i 0
  have hcell (i : Nat) (hi : i < payloads.length) :
      cellAt R s d i = some (x i, x (i + 1)) := by
    have hi' : i + 1 < (canonicalPoints R s d).length := by omega
    have hi0 : i < (canonicalPoints R s d).length := by omega
    simp [x, cellAt, List.getElem?_eq_getElem, hi', hi0, List.getD_eq_getElem]
  have hfirst' : x 0 = supportHullLower R s := by
    simp only [x, List.getD_eq_getElem?_getD, hfirst, Option.getD_some]
  have hlast' : x payloads.length = supportHullUpper R s := by
    simp only [x, List.getD_eq_getElem?_getD, hlast, Option.getD_some]
  let g : Real → Real := fun y => Complex.normSq (f y - f (y - s))
  have hc : Continuous g :=
    Complex.continuous_normSq.comp
      (f.continuous.sub (f.continuous.comp (continuous_id.sub continuous_const)))
  have hr : (0 : Real) < R := by exact_mod_cast hR
  have hz (y : Real) (hy : 2 * (R : Real) ≤ |y|) : f y = 0 := by
    rw [hf y]
    have ht : 2 - |y| / R ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hr]
      exact hy
    rw [Real.smoothTransition.zero_of_nonpos ht]
    simp
  have hlo₁ : (supportHullLower R s : Real) ≤ -(2 * (R : Real)) := by
    unfold supportHullLower
    exact_mod_cast (min_le_left (-(2 * (R : Rat))) (s - 2 * (R : Rat)))
  have hlo₂ : (supportHullLower R s : Real) ≤ (s : Real) - 2 * R := by
    unfold supportHullLower
    exact_mod_cast (min_le_right (-(2 * (R : Rat))) (s - 2 * (R : Rat)))
  have hup₁ : 2 * (R : Real) ≤ (supportHullUpper R s : Real) := by
    unfold supportHullUpper
    exact_mod_cast (le_max_left (2 * (R : Rat)) (s + 2 * (R : Rat)))
  have hup₂ : (s : Real) + 2 * R ≤ (supportHullUpper R s : Real) := by
    unfold supportHullUpper
    exact_mod_cast (le_max_right (2 * (R : Rat)) (s + 2 * (R : Rat)))
  have hsupp : Function.support g ⊆
      Ioc (supportHullLower R s : Real) (supportHullUpper R s : Real) := by
    intro y hy
    constructor
    · by_contra h
      have hyl : y ≤ (supportHullLower R s : Real) := le_of_not_gt h
      have hy₁ : 2 * (R : Real) ≤ |y| := by linarith [neg_le_abs y]
      have hy₂ : 2 * (R : Real) ≤ |y - s| := by linarith [neg_le_abs (y - s)]
      simp [Function.mem_support, g, hz y hy₁, hz (y - s) hy₂] at hy
    · by_contra h
      have hyu : (supportHullUpper R s : Real) < y := lt_of_not_ge h
      have hy₁ : 2 * (R : Real) ≤ |y| := by linarith [le_abs_self y]
      have hy₂ : 2 * (R : Real) ≤ |y - s| := by linarith [le_abs_self (y - s)]
      simp [Function.mem_support, g, hz y hy₁, hz (y - s) hy₂] at hy
  have hsum : (∑ i ∈ Finset.range payloads.length,
      ∫ y in (x i : Real)..(x (i + 1) : Real), g y) = translationEnergy f s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun i _ => hc.intervalIntegrable _ _)]
    rw [hfirst', hlast', intervalIntegral.integral_eq_integral_of_support_subset hsupp]
    rfl
  have hlocal (i : Nat) (hi : i ∈ Finset.range payloads.length) :=
    checked_canonical_cell_integral_encloses R p q s pcs qcs hpcs hqcs
      d i m n (payloads.getD i defaultPayload) (x i) (x (i + 1))
      (hcell i (Finset.mem_range.mp hi)) (hchecks i (Finset.mem_range.mp hi)) f hf
  have hl := Finset.sum_le_sum (fun i hi => (hlocal i hi).1)
  have hu := Finset.sum_le_sum (fun i hi => (hlocal i hi).2)
  have hloEq : ((aggregateBounds R s d payloads).1 : Real) =
      ∑ i ∈ Finset.range payloads.length,
        (((x (i + 1) - x i) * (payloads.getD i defaultPayload).norm.total.1 : Rat) : Real) := by
    simp only [aggregateBounds, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcell i (Finset.mem_range.mp hi)]
  have hupEq : ((aggregateBounds R s d payloads).2 : Real) =
      ∑ i ∈ Finset.range payloads.length,
        (((x (i + 1) - x i) * (payloads.getD i defaultPayload).norm.total.2 : Rat) : Real) := by
    simp only [aggregateBounds, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcell i (Finset.mem_range.mp hi)]
  exact ⟨by simpa only [hloEq, hsum, g] using hl,
    by simpa only [hupEq, hsum, g] using hu, hwidth⟩


#print axioms checked_literal_translation_energy_sound

end D5.S3.Weil.Separator.TranslationEnergy
