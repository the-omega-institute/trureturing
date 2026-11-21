/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/JetMask
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Packed integer sign checks for the scalar certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreePackedCheck
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Basic.Real.Basic

namespace RefinedBMV.DimThree.PackedCheck

open scoped BigOperators

private theorem packSigned_ofFn_eq_sum (base : ℤ) (n : ℕ) (f : ℕ → ℤ) :
    packSigned base (List.ofFn fun i : Fin n => f i) =
      ∑ i ∈ Finset.range n, f i * base ^ i := by
  induction n generalizing f with
  | zero => simp [packSigned]
  | succ n ih =>
    simp only [List.ofFn_succ, packSigned, Fin.val_zero, Fin.val_succ]
    rw [ih (fun i => f (i + 1)),
      Finset.sum_range_succ', Finset.mul_sum]
    rw [pow_zero, mul_one, add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ', mul_left_comm]

/-- The coefficient list, in ascending order, packs to one integer evaluation. -/
theorem packSigned_coeff_eq_eval (P : Polynomial ℤ) {n : ℕ}
    (hdeg : P.natDegree < n) (base : ℤ) :
    packSigned base (List.ofFn fun i : Fin n => P.coeff i) = P.eval base :=
  (packSigned_ofFn_eq_sum base n P.coeff).trans (P.eval_eq_sum_range' hdeg base).symm

/-- The high bit in each of the `n` base-`2^(w+1)` digits. -/
def polynomialMask (w n : ℕ) : ℕ :=
  packDigits (2 ^ (w + 1)) (List.replicate n (2 ^ w))

theorem coeff_nonneg_of_polynomial_mask (P : Polynomial ℤ) {n w : ℕ}
    (hdeg : P.natDegree < n)
    (hbound : ∀ i, -(2 : ℤ) ^ w ≤ P.coeff i ∧ P.coeff i < (2 : ℤ) ^ w)
    (hcheck : (P.eval (2 ^ (w + 1)) + ↑(polynomialMask w n)).toNat &&&
      polynomialMask w n = polynomialMask w n) :
    ∀ i, 0 ≤ P.coeff i := by
  let cs := List.ofFn fun i : Fin n => P.coeff i
  have hcs : ∀ c ∈ cs, -((2 ^ w : ℕ) : ℤ) ≤ c ∧ c < ((2 ^ w : ℕ) : ℤ) := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact hbound i
  have hmask : packDigits (2 ^ (w + 1)) (List.replicate cs.length (2 ^ w)) =
      polynomialMask w n := by
    simp [cs, polynomialMask]
  have hshift := packDigits_shift (2 ^ (w + 1)) (2 ^ w) cs (fun c hc => (hcs c hc).1)
  rw [hmask, packSigned_coeff_eq_eval P hdeg] at hshift
  have htest := congrArg Int.toNat hshift
  simp only [Int.toNat_natCast] at htest
  intro i
  by_cases hi : i < n
  · exact digit_signs_of_mask w cs hcs (by rwa [hmask, htest]) _
      (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩)
  · rw [P.coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_gt hi))]

/-- A successful packed mask check gives nonnegative evaluation on the real half-line. -/
theorem eval₂_nonneg_of_polynomial_mask (P : Polynomial ℤ) {n w : ℕ}
    (hdeg : P.natDegree < n)
    (hbound : ∀ i, -(2 : ℤ) ^ w ≤ P.coeff i ∧ P.coeff i < (2 : ℤ) ^ w)
    (hcheck : (P.eval (2 ^ (w + 1)) + ↑(polynomialMask w n)).toNat &&&
      polynomialMask w n = polynomialMask w n)
    (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ P.eval₂ (Int.castRingHom ℝ) z := by
  rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℝ) hdeg z]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Int.cast_nonneg (coeff_nonneg_of_polynomial_mask P hdeg hbound hcheck i))
      (pow_nonneg hz i)

end RefinedBMV.DimThree.PackedCheck
