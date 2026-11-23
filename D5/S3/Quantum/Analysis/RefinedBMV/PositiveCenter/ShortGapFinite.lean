/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapFinite
   generality: S
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Bernstein coefficients for the scalar short-gap series. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapRows
import Batteries.Tactic.OpenPrivate

/-! Bernstein inequalities for the finite short-gap rows. -/

open Finset
open Polynomial (C)
open scoped Polynomial

namespace RefinedBMV.PositiveCenter.ShortGapFinite

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

open private choose choose_eq add sub scale mul polynomial_add polynomial_sub
  polynomial_scale polynomial_mul sumCoeffs polynomial_sum h derivative
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapRows

-- Witnesses, coefficient correspondence, and the representative benchmark.
namespace Revised

open private jetFrom fastU fastT fastJet fastJet_eq fastSpacingL1_eq
  uProjection tProjection curvatureRow25PowerData from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapRows

/-- Ascending x rows of q. Each row is an ascending list in y. -/
def qRows : List Coefficients :=
  [[1060364, 289300, 8719], [1201564, 346575, 15251], [882548, 320739, 26395],
    [457271, 181003, 14742], [374350, 251002, 50057], [-59873, -84643, -25991],
    [141041, 120222, 28731]].map (scale (1 / 1000000))

/-- Ascending x rows of r. -/
def rRows : List Coefficients := [[1124, 16], [442, 119]].map (scale (1 / 1000))

private def shiftX (a : ℕ → Coefficients) (n : ℕ) : Coefficients :=
  if n = 0 then [] else a (n - 1)

private theorem shiftX_polynomial (a : ℕ → Coefficients) (n : ℕ) :
    polynomial (shiftX a n) = if n = 0 then 0 else polynomial (a (n - 1)) := by
  by_cases hn : n = 0 <;> simp [shiftX, hn, polynomial]

/-- Convolve with a short witness in x using the existing y polynomial multiplication. -/
private def witnessProduct
    (w : List Coefficients) (a : ℕ → Coefficients) (n : ℕ) : Coefficients :=
  sumCoeffs (fun k => mul (w.getD k []) (a (n - k))) (min w.length (n + 1))

private theorem witnessProduct_polynomial
    (w : List Coefficients) (a : ℕ → Coefficients) (n : ℕ) :
    polynomial (witnessProduct w a n) =
      ∑ k ∈ range (n + 1), polynomial (w.getD k []) * polynomial (a (n - k)) := by
  rw [witnessProduct, polynomial_sum]
  simp only [polynomial_mul]
  apply Finset.sum_subset
  · intro k hk
    exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (Nat.min_le_right _ _))
  · intro k hk hout
    have hk' := mem_range.mp hk
    have hout' : ¬ k < min w.length (n + 1) := fun h => hout (mem_range.mpr h)
    have hlen : w.length ≤ k := by omega
    have hget : w[k]? = none := List.getElem?_eq_none hlen
    simp [List.getD_eq_getElem?_getD, hget, polynomial]

/-- x power rows of P₀ − b₀ − q². -/
def sqrtComparison (n : ℕ) : Coefficients :=
  sub (sub (jetRow .value n) (budgetRow .value n))
    (witnessProduct qRows (fun k => qRows.getD k []) n)

/-- x power rows of the second tensor in the order-18 certificate. -/
def curvatureComparison (n : ℕ) : Coefficients :=
  let corrected := witnessProduct qRows
    (fun k => sub (jetRow .corrected k) (budgetRow .corrected k)) n
  let first := sub (jetRow .first n) (shiftX (witnessProduct rRows (jetRow .first)) n)
  let second := shiftX (jetRow .second) n
  let value := scale (1 / 2) (shiftX (witnessProduct rRows
    (witnessProduct rRows (jetRow .value))) n)
  let error := add (add (budgetRow .first n) (budgetRow .second n))
    (scale 2 (budgetRow .value n))
  sub (sub corrected (add (add first second) value)) error

/-- Coefficient identity for the first tensor, with each row interpreted as a polynomial in y. -/
theorem sqrtComparison_row_polynomial (n : ℕ) :
    polynomial (sqrtComparison n) =
      polynomial (jetRow .value n) - polynomial (budgetRow .value n) -
        ∑ k ∈ range (n + 1), polynomial (qRows.getD k []) *
          polynomial (qRows.getD (n - k) []) := by
  simp only [sqrtComparison, polynomial_sub, witnessProduct_polynomial]

/-- Coefficient identity for the second tensor. The three terms guarded by n = 0
have an explicit factor x in the polynomial. All products here are in the y variable. -/
theorem curvatureComparison_row_polynomial (n : ℕ) :
    let P (g : Jet) (k : ℕ) := polynomial (jetRow g k)
    let b (g : Jet) (k : ℕ) := polynomial (budgetRow g k)
    let q (k : ℕ) := polynomial (qRows.getD k [])
    let r (k : ℕ) := polynomial (rRows.getD k [])
    let z := n - 1
    polynomial (curvatureComparison n) =
      (∑ k ∈ range (n + 1), q k * (P .corrected (n - k) - b .corrected (n - k))) -
        ((P .first n - (if n = 0 then 0 else
            ∑ k ∈ range (z + 1), r k * P .first (z - k))) +
          (if n = 0 then 0 else P .second z) +
          C (1 / 2 : ℚ) * (if n = 0 then 0 else
            ∑ k ∈ range (z + 1), r k *
              ∑ l ∈ range (z - k + 1), r l * P .value (z - k - l))) -
        (b .first n + b .second n + C (2 : ℚ) * b .value n) := by
  simp only [curvatureComparison, polynomial_add, polynomial_sub, polynomial_scale,
    shiftX_polynomial, witnessProduct_polynomial]

/-- Evaluate at x = 1, keeping the remaining y coefficients. -/
def atOne (a : ℕ → Coefficients) : Coefficients := sumCoeffs a 20

/-- L at x = 1. -/
def endpointL : Coefficients :=
  scale 2 (sub (add (atOne (jetRow .value)) (atOne (jetRow .first)))
    (add (atOne (budgetRow .value)) (atOne (budgetRow .first))))

/-- M at x = 1. -/
def endpointM : Coefficients := add (atOne (jetRow .value)) (atOne (budgetRow .value))

/-- V at x = 1. -/
def endpointV : Coefficients := atOne (jetRow .slope)

/-- L² − 4M(V + bS(1))², as a polynomial in y. -/
def endpointComparison : Coefficients :=
  let s := add endpointV (atOne (budgetRow .slope))
  sub (mul endpointL endpointL) (scale 4 (mul endpointM (mul s s)))

theorem atOne_polynomial (a : ℕ → Coefficients) :
    polynomial (atOne a) = ∑ k ∈ range 20, polynomial (a k) := polynomial_sum _ _

theorem endpointL_polynomial :
    polynomial endpointL = C (2 : ℚ) *
      ((polynomial (atOne (jetRow .value)) + polynomial (atOne (jetRow .first))) -
        (polynomial (atOne (budgetRow .value)) + polynomial (atOne (budgetRow .first)))) := by
  simp only [endpointL, polynomial_scale, polynomial_sub, polynomial_add]

theorem endpointM_polynomial :
    polynomial endpointM =
      polynomial (atOne (jetRow .value)) + polynomial (atOne (budgetRow .value)) := by
  simp only [endpointM, polynomial_add]

theorem endpointV_polynomial :
    polynomial endpointV = polynomial (atOne (jetRow .slope)) := rfl

theorem endpointComparison_polynomial :
    polynomial endpointComparison = polynomial endpointL ^ 2 -
      C (4 : ℚ) * (polynomial endpointM *
        (polynomial endpointV + polynomial (atOne (budgetRow .slope))) ^ 2) := by
  simp only [endpointComparison, polynomial_sub, polynomial_mul, polynomial_scale,
    polynomial_add, pow_two]

/-- Elevate in x to degree d, retaining each row's y power coefficients. -/
def bernsteinXRow (a : ℕ → Coefficients) (d i : ℕ) : Coefficients :=
  sumCoeffs (fun k => scale ((choose i k : ℚ) / (choose d k : ℚ)) (a k))
    (min (d + 1) (i + 1))

/-- The x row is the coefficientwise Bernstein transform, with y left in the power basis. -/
theorem bernsteinXRow_polynomial (a : ℕ → Coefficients) (d i : ℕ) :
    polynomial (bernsteinXRow a d i) =
      ∑ k ∈ range (d + 1), C ((i.choose k : ℚ) / (d.choose k : ℚ)) * polynomial (a k) := by
  rw [bernsteinXRow, polynomial_sum]
  simp only [polynomial_scale, choose_eq]
  apply Finset.sum_subset
  · intro k hk
    exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (Nat.min_le_left _ _))
  · intro k hk hout
    have hk' := mem_range.mp hk
    have hout' : ¬ k < min (d + 1) (i + 1) := fun h => hout (mem_range.mpr h)
    have hik : i < k := by omega
    simp [Nat.choose_eq_zero_of_lt hik]

/-- The tensor coefficient at (i,j), via two ordinary Bernstein transforms. -/
def tensorBernstein (a : ℕ → Coefficients) (d e i j : ℕ) : ℚ :=
  bernstein (bernsteinXRow a d i) e j

/-- The final y transform is the existing polynomial Bernstein coefficient. -/
theorem tensorBernstein_eq (a : ℕ → Coefficients) (d e i j : ℕ) :
    (tensorBernstein a d e i j : ℂ) =
      bernsteinCoefficient e j
        ((∑ k ∈ range (d + 1), C ((i.choose k : ℚ) / (d.choose k : ℚ)) *
          polynomial (a k)).map (Rat.castHom ℂ)) := by
  rw [tensorBernstein, bernstein_eq, bernsteinXRow_polynomial]

private def strictRow (a : Coefficients) (e : ℕ) (bound : ℚ) : Bool :=
  (List.range (e + 1)).all fun j => decide (bound < bernstein a e j)

private theorem strictRow_sound {a : Coefficients} {e j : ℕ} {bound : ℚ}
    (h : strictRow a e bound = true) (hj : j ≤ e) : bound < bernstein a e j := by
  rw [strictRow, List.all_eq_true] at h
  exact of_decide_eq_true (h j (List.mem_range.mpr (Nat.lt_succ_of_le hj)))

private def sqrtRowCheck (i : ℕ) : Bool := strictRow (bernsteinXRow sqrtComparison 19 i) 6 (3 / 5000)
private def curvatureRowCheck (i : ℕ) : Bool :=
  strictRow (bernsteinXRow curvatureComparison 25 i) 8 (7 / 2000)

-- Isolated first kernel benchmark. This computes the nine y power coefficients once.
set_option maxHeartbeats 2000000 in
set_option profiler true in
set_option profiler.threshold 0 in
private theorem curvatureRow25_power_eq :
    bernsteinXRow curvatureComparison 25 25 = curvatureRow25PowerData := by
  decide +kernel

-- The next benchmark measures just the nine y Bernstein inequalities.
set_option maxHeartbeats 2000000 in
set_option profiler true in
set_option profiler.threshold 0 in
private theorem curvatureRow25_checked : curvatureRowCheck 25 = true := by
  rw [curvatureRowCheck, curvatureRow25_power_eq]
  decide +kernel

/-- The representative row at the right edge of the x rectangle. -/
theorem curvatureBernstein_row25 {j : ℕ} (hj : j ≤ 8) :
    (7 / 2000 : ℚ) < tensorBernstein curvatureComparison 25 8 25 j :=
  strictRow_sound curvatureRow25_checked hj

end Revised

namespace Revised

open private jetFrom fastU fastT fastJet fastJet_eq fastSpacingL1_eq
  uProjection tProjection curvatureRow25PowerData from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapRows

set_option maxHeartbeats 2000000 in
private theorem uProjection_eq (n : ℕ) (hn : n < 21) :
    uProjection.getD n [] = (fastU n).take 7 := by
  interval_cases n <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem tProjection_eq (n : ℕ) (hn : n < 21) :
    tProjection.getD n [] = (fastT n).take 7 := by
  interval_cases n <;> decide +kernel

private theorem take_scale (z : ℚ) (a : Coefficients) :
    (scale z a).take 7 = scale z (a.take 7) := by
  exact List.map_take.symm

private theorem take_sub_single (a : Coefficients) (z : ℚ) :
    (sub a [z]).take 7 = sub (a.take 7) [z] := by
  cases a with
  | nil => rfl
  | cons a as =>
    simp only [sub, List.take, List.zipWithAll_cons_cons, List.zipWithAll_nil, List.map_take]

/-- Each stored primitive row agrees with the exact Faulhaber row in y degrees 0 through 6. -/
theorem jetRow_eq_take (g : Jet) (n : ℕ) (hn : n < 19) :
    jetRow g n = (fullJet g n).take 7 := by
  have hu₀ := uProjection_eq n (by omega)
  have hu₁ := uProjection_eq (n + 1) (by omega)
  have hu₂ := uProjection_eq (n + 2) (by omega)
  have ht₁ := tProjection_eq (n + 1) (by omega)
  have ht₂ := tProjection_eq (n + 2) (by omega)
  rw [jetRow, if_pos hn, ← fastJet_eq g n hn]
  by_cases hzero : n = 0
  · cases g <;>
      simp only [fastJet, jetFrom, derivative, hu₀, hu₁, hu₂, ht₁, ht₂,
        ← take_scale, ← take_sub_single, if_pos hzero]
  · cases g <;>
    simp only [fastJet, jetFrom, derivative, hu₀, hu₁, hu₂, ht₁, ht₂,
      ← take_scale, if_neg hzero]

set_option maxHeartbeats 2000000 in
/-- All five ℓ¹ bounds for the discarded spacing coefficients. -/
theorem spacingL1_le (g : Jet) :
    spacingL1 g ≤ (spacingNumerator g : ℚ) / 1000000 := by
  rw [← fastSpacingL1_eq]
  cases g <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem sqrtRow_checked (i : ℕ) (hi : i ≤ 19) : sqrtRowCheck i = true := by
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem curvatureRow_checked (i : ℕ) (hi : i ≤ 25) :
    curvatureRowCheck i = true := by
  have hedge : i ≤ 24 ∨ i = 25 := by omega
  rcases hedge with hi' | rfl
  · interval_cases i <;> decide +kernel
  · exact curvatureRow25_checked

/-- All 140 entries of the first tensor exceed the proposed lower bound. -/
theorem sqrtBernstein_checked {i j : ℕ} (hi : i ≤ 19) (hj : j ≤ 6) :
    (3 / 5000 : ℚ) < tensorBernstein sqrtComparison 19 6 i j :=
  strictRow_sound (sqrtRow_checked i hi) hj

/-- All 234 entries of the second tensor exceed the proposed lower bound. -/
theorem curvatureBernstein_checked {i j : ℕ} (hi : i ≤ 25) (hj : j ≤ 8) :
    (7 / 2000 : ℚ) < tensorBernstein curvatureComparison 25 8 i j :=
  strictRow_sound (curvatureRow_checked i hi) hj

set_option maxHeartbeats 2000000 in
private theorem endpointComparison_checked : strictRow endpointComparison 18 446 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private theorem endpointL_checked : strictRow endpointL 6 84 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
private theorem endpointV_checked : strictRow endpointV 6 10 = true := by decide +kernel

/-- The 19 endpoint Bernstein coefficients for the sign comparison. -/
theorem endpointBernstein_checked {j : ℕ} (hj : j ≤ 18) :
    (446 : ℚ) < bernstein endpointComparison 18 j :=
  strictRow_sound endpointComparison_checked hj

/-- The seven endpoint Bernstein coefficients for L. -/
theorem endpointLBernstein_checked {j : ℕ} (hj : j ≤ 6) : (84 : ℚ) < bernstein endpointL 6 j :=
  strictRow_sound endpointL_checked hj

/-- The seven endpoint Bernstein coefficients for V. -/
theorem endpointVBernstein_checked {j : ℕ} (hj : j ≤ 6) : (10 : ℚ) < bernstein endpointV 6 j :=
  strictRow_sound endpointV_checked hj

/-- The row lengths bound the spacing degree used in the Bernstein transform. -/
theorem sqrtBernstein_row_length {i : ℕ} (hi : i ≤ 19) :
    (bernsteinXRow sqrtComparison 19 i).length ≤ 7 := by
  interval_cases i <;> decide +kernel

theorem curvatureBernstein_row_length {i : ℕ} (hi : i ≤ 25) :
    (bernsteinXRow curvatureComparison 25 i).length ≤ 9 := by
  interval_cases i <;> decide +kernel

theorem endpoint_row_lengths : endpointComparison.length ≤ 19 ∧
    endpointL.length ≤ 7 ∧ endpointV.length ≤ 7 := by decide +kernel

#print axioms curvatureBernstein_row25
#print axioms jetRow_eq_take
#print axioms spacingL1_le
#print axioms sqrtBernstein_checked
#print axioms curvatureBernstein_checked
#print axioms endpointBernstein_checked
#print axioms endpointLBernstein_checked
#print axioms endpointVBernstein_checked

end Revised

end RefinedBMV.PositiveCenter.ShortGapFinite
