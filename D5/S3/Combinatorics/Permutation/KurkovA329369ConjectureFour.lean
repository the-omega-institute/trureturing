/- GID: D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal A358612 array gives the signed factorial-power formula for A329369. -/

import D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
import D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm
import D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet

/-! The Pochhammer expansion and signed factorial-power evaluation for A329369. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour

open Polynomial
open scoped BigOperators
open D5.S1.Digit.DyadicRowPolynomialRecurrence (R wt)
open D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T)
open D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm (b)
open D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient

noncomputable section

private theorem row_expansion (k : ℕ) :
    rowPolynomial k = ∑ i ∈ Finset.Icc 1 (wt k + 2),
      ((-1 : ℚ) ^ (wt k + 2 - i) * T k i) • ascPochhammer ℚ i := by
  classical
  apply pochhammerBasis.ext_elem
  intro j
  change pochhammerBasis.coord j (rowPolynomial k) = pochhammerBasis.coord j _
  have hc : pochhammerBasis.coord j (rowPolynomial k) =
      (-1 : ℚ) ^ (wt k + 2 - j) * T k j := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact source_coordinate 0 j
    · exact ((positiveEvenCoefficient k 2 hk le_rfl).2 j).2
  simp only [map_sum, map_smul, coord_basis, smul_eq_mul]
  by_cases hj : j ∈ Finset.Icc 1 (wt k + 2)
  · rw [Finset.sum_eq_single_of_mem j hj]
    · simpa using hc
    · intro i _ hij
      simp [hij]
  · have hz : T k j = 0 := by
      by_cases h0 : j = 0
      · subst j
        rw [T, ite_eq_left rfl]
      · apply D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.support
        simp only [Finset.mem_Icc, not_and_or] at hj
        omega
    rw [hc, hz, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]

private theorem dyadic_expansion (m k : ℕ) :
    rationalRow (2 ^ m * (2 * k + 1)) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (((-1 : ℚ) ^ (wt k + 2 - i) * T k i) * (i : ℚ) ^ m) •
          ascPochhammer ℚ i := by
  induction m with
  | zero =>
    simpa [rationalRow_odd, rowPolynomial] using row_expansion k
  | succ m ih =>
    rw [show 2 ^ (m + 1) * (2 * k + 1) = 2 * (2 ^ m * (2 * k + 1)) by ring,
      rationalRow_even _ (by positivity), ih, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, difference_pochhammer, smul_smul, pow_succ, mul_assoc]

private theorem ascPochhammer_eval_one (i : ℕ) :
    (ascPochhammer ℚ i).eval 1 = (i.factorial : ℚ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [ascPochhammer_succ_right, eval_mul, ih, Nat.factorial_succ, Nat.cast_mul]
    simp
    ring

private theorem source_sign (w i : ℕ) (hi : i ≤ w + 2) :
    (-1 : ℚ) ^ (w + 2 - i) = (-1 : ℚ) ^ ((w : ℤ) - (i : ℤ)) := by
  have he : ((w + 2 - i : ℕ) : ℤ) = (w : ℤ) - (i : ℤ) + 2 := by omega
  rw [← zpow_natCast, he, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
  norm_num

private theorem b_factorial_sum (m k : ℕ) :
    (b (2 ^ m * (2 * k + 1)) : ℚ) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (i.factorial : ℚ) * (i : ℚ) ^ m * T k i *
          (-1 : ℚ) ^ ((wt k : ℤ) - (i : ℤ)) := by
  have heval (n : ℕ) : (rationalRow n).eval 1 = (b n : ℚ) := by
    simp [rationalRow, b]
  rw [← heval, dyadic_expansion, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_smul, ascPochhammer_eval_one, source_sign _ _ (Finset.mem_Icc.mp hi).2]
  simp only [smul_eq_mul]
  ring


open AdjacentExcedanceSet

/-- Width `w` uses positions `1,…,w+1`. A zero-based position `j` below the last
position reads bit `w-1-j`. -/
def binaryExcedances (w n : ℕ) : Set (Fin (w + 1)) :=
  {j | j.val < w ∧ n.testBit (w - 1 - j.val) = true}

/-- The strict-excedance count for the width-`w` padded binary expansion of `n`. -/
def paddedCount (w n : ℕ) : ℕ :=
  exactCount (binaryExcedances w n)

private theorem count_delete_zero {n : ℕ} (S : Set (Fin (n + 2)))
    (h0 : (0 : Fin (n + 2)) ∉ S) :
    exactCount S = exactCount (Fin.succ ⁻¹' S) := by
  let e : ExactPermutations S ≃ {p : ExactPermutations S // p.val 0 = 0} :=
    { toFun := fun p => ⟨p, Fin.ext (Nat.eq_zero_of_le_zero (le_of_not_gt
        (fun h => h0 ((p.property 0).mp h))))⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [exactCount, Fin.succAbove_zero] using
    Nat.card_congr (e.trans (deleteFixedCase 0 S h0))

private theorem paddedCount_succ {w n : ℕ} (hn : n < 2 ^ w) :
    paddedCount (w + 1) n = paddedCount w n := by
  have hz : (0 : Fin (w + 2)) ∉ binaryExcedances (w + 1) n := by
    simp [binaryExcedances, Nat.testBit_lt_two_pow hn]
  unfold paddedCount
  rw [count_delete_zero _ hz]
  congr 1
  ext j
  change (j.val + 1 < w + 1 ∧ n.testBit (w + 1 - 1 - (j.val + 1)) = true) ↔ _
  have hj : w + 1 - 1 - (j.val + 1) = w - 1 - j.val := by omega
  rw [hj]
  simp [binaryExcedances]

private theorem paddedCount_zero (w : ℕ) : paddedCount w 0 = 1 := by
  induction w with
  | zero =>
    let e : ExactPermutations (binaryExcedances 0 0) ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨Equiv.refl _, by simp [HasExactExcedances, binaryExcedances]⟩
        left_inv := fun _ => Subtype.ext (Equiv.ext fun i => by
          apply Fin.ext
          change (_ : Fin (0 + 1)).val = _
          have (x : Fin (0 + 1)) : x.val = 0 := by have := x.isLt; omega
          simp only [this])
        right_inv := fun _ => Subsingleton.elim _ _ }
    simpa [paddedCount, exactCount] using Nat.card_congr e
  | succ w ih => rw [paddedCount_succ (Nat.two_pow_pos w), ih]

private theorem count_delete_trailing {w : ℕ} (S : Set (Fin (w + 2)))
    (hl : (Fin.last w).castSucc ∈ S) (hr : (Fin.last w).succ ∉ S) :
    exactCount S = exactCount ((Fin.last w).castSucc.succAbove ⁻¹' S) := by
  let a := Fin.last w
  let hitsLast : ExactPermutations S ≃ {p : Equiv.Perm (Fin (w + 2)) //
      HasExactExcedances p S ∧ p a.castSucc = a.succ} :=
    { toFun := fun p => ⟨p.val, p.property, by
        have hp := (p.property a.castSucc).mpr hl
        have hval := (p.val a.castSucc).isLt
        apply Fin.ext
        change w < (p.val a.castSucc).val at hp
        change (p.val a.castSucc).val = w + 1
        omega⟩
      invFun := fun p => ⟨p.val, p.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let reorder :
      {p : Equiv.Perm (Fin (w + 2)) // HasExactExcedances p (S \ {a.castSucc}) ∧
        p a.succ = a.succ} ≃ {p : ExactPermutations (S \ {a.castSucc}) //
          p.val a.succ = a.succ} :=
    { toFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      invFun := fun p => ⟨p.val.val, p.val.property, p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr (hitsLast.trans
    (((swapPositions a.castSucc a.succ).subtypeEquiv (exact_swap_fixed_iff a S hl hr)).trans
      (reorder.trans (deleteFixedCase a.succ _ (fun h => hr h.1)))))
  change exactCount S = exactCount (a.succ.succAbove ⁻¹' (S \ {a.castSucc})) at h
  rwa [delete_swap_set a S hr] at h

private theorem paddedCount_odd (w n : ℕ) :
    paddedCount (w + 1) (2 * n + 1) = paddedCount w n := by
  let a := Fin.last w
  have hl : a.castSucc ∈ binaryExcedances (w + 1) (2 * n + 1) := by
    change w < w + 1 ∧ (2 * n + 1).testBit (w + 1 - 1 - w) = true
    have h : (2 * n + 1) % 2 = 1 := by omega
    simp [h]
  have hr : a.succ ∉ binaryExcedances (w + 1) (2 * n + 1) := by
    change ¬ (w + 1 < w + 1 ∧ _)
    simp
  unfold paddedCount
  rw [count_delete_trailing _ hl hr]
  congr 1
  ext j
  change a.castSucc.succAbove j ∈ binaryExcedances (w + 1) (2 * n + 1) ↔
    j ∈ binaryExcedances w n
  by_cases hj : j.val < w
  · have hj' : j < a := hj
    rw [Fin.succAbove_castSucc_of_lt _ _ hj']
    change (j.val < w + 1 ∧ (2 * n + 1).testBit (w + 1 - 1 - j.val) = true) ↔
      (j.val < w ∧ n.testBit (w - 1 - j.val) = true)
    rw [show w + 1 - 1 - j.val = (w - 1 - j.val) + 1 by omega, Nat.testBit_succ]
    simp [show (2 * n + 1) / 2 = n by omega, hj, show j.val < w + 1 by omega]
  · have he : j = a := Fin.ext (by have := j.isLt; change j.val = w; omega)
    subst j
    rw [Fin.succAbove_castSucc_self]
    exact iff_of_false hr (by change ¬ (w < w ∧ _); simp)

end
end D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
