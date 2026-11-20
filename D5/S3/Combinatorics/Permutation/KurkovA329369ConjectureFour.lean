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
open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt)
open D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T)
open D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm (b b_zero b_even_index b_odd_index)
open D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient

noncomputable section

private theorem row_expansion (k : ℕ) :
    rowPolynomial k = ∑ i ∈ Finset.Icc 1 (wt k + 2),
      ((-1 : ℚ) ^ (wt k + 2 - i) * T k i) • ascPochhammer ℚ i := by
  classical
  apply pochhammerBasis.ext_elem
  intro j
  change pochhammerBasis.coord j (rowPolynomial k) = pochhammerBasis.coord j _
  have hc := source_coordinate k j
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
  rw [eval_smul, _root_.ascPochhammer_eval_one ℚ i, source_sign _ _ (Finset.mem_Icc.mp hi).2]
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


private theorem mem_binaryExcedances_suffix {w q h b : ℕ} (hq : q ≤ w)
    (hb : b < 2 ^ q) (j : Fin (w + 1)) :
    j ∈ binaryExcedances w (2 ^ q * h + b) ↔
      (j.val < w - q ∧ h.testBit (w - q - 1 - j.val) = true) ∨
        (w - q ≤ j.val ∧ j.val < w ∧ b.testBit (w - 1 - j.val) = true) := by
  change (j.val < w ∧ (2 ^ q * h + b).testBit (w - 1 - j.val) = true) ↔ _
  rw [Nat.testBit_two_pow_mul_add h hb]
  by_cases hj : j.val < w - q
  · rw [ite_eq_right (by omega), show w - 1 - j.val - q = w - q - 1 - j.val by omega]
    simp [hj, show j.val < w by omega, show ¬w - q ≤ j.val by omega]
  · by_cases hlast : j.val < w
    · rw [ite_eq_left (by omega)]
      simp [hj, hlast, show w - q ≤ j.val by omega]
    · simp [hj, hlast]

private theorem mem_binaryExcedances_single_bit {w q h t : ℕ} (hq : q ≤ w)
    (ht : t < q) (j : Fin (w + 1)) :
    j ∈ binaryExcedances w (2 ^ q * h + 2 ^ t) ↔
      (j.val < w - q ∧ h.testBit (w - q - 1 - j.val) = true) ∨
        j.val = w - 1 - t := by
  rw [mem_binaryExcedances_suffix hq ((Nat.pow_lt_pow_iff_right (by decide)).mpr ht)]
  simp only [Nat.testBit_two_pow, decide_eq_true_eq]
  exact or_congr Iff.rfl ⟨fun h => by omega, fun h => by omega⟩

private theorem paddedCount_even {w n : ℕ} (hn : 0 < n) (hw : 2 * n < 2 ^ (w + 1)) :
    paddedCount (w + 1) (2 * n) =
      paddedCount (w + 1) (2 * n - 2 ^ padicValNat 2 n) +
        paddedCount w n + paddedCount w (n - 2 ^ padicValNat 2 n) := by
  let r := padicValNat 2 n
  let h := D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.h n
  have index : n = 2 ^ r * (2 * h + 1) :=
    D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.dyadic_index n hn
  have lower : 2 ^ r ≤ n := by
    rw [index]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have lowerDouble : 2 ^ (r + 1) ≤ 2 * n := by
    rw [pow_succ, Nat.mul_comm]
    omega
  have hrw : r + 1 < w + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp (lowerDouble.trans_lt hw)
  let a : Fin (w + 1) := ⟨w - (r + 1), by omega⟩
  let fromPrefix (j : ℕ) : Prop := j < a.val ∧ h.testBit (a.val - 1 - j) = true
  have hn' : n = 2 ^ (r + 1) * h + 2 ^ r := by
    calc
      n = 2 ^ r * (2 * h + 1) := index
      _ = _ := by rw [pow_succ]; ring
  have he : 2 * n = 2 ^ (r + 2) * h + 2 ^ (r + 1) := by
    rw [hn', show r + 2 = (r + 1) + 1 by omega, pow_succ]
    ring
  have hs : 2 * n - 2 ^ r = 2 ^ (r + 2) * h + 2 ^ r := by
    rw [he, pow_succ (2 : ℕ) r]
    omega
  have hd : n - 2 ^ r = 2 ^ (r + 1) * h := by omega
  have evenMem (j : Fin (w + 2)) :
      j ∈ binaryExcedances (w + 1) (2 * n) ↔ fromPrefix j.val ∨ j = a.castSucc := by
    rw [he, mem_binaryExcedances_single_bit (by omega) (by omega)]
    change (_ ∨ j.val = w + 1 - 1 - (r + 1)) ↔ fromPrefix j.val ∨ j = a.castSucc
    rw [Fin.ext_iff]
    have e : w + 1 - (r + 2) = a.val := by dsimp [a]; omega
    simp only [e, Nat.add_sub_cancel, fromPrefix, Fin.val_castSucc, a]
  have swappedMem (j : Fin (w + 2)) :
      j ∈ binaryExcedances (w + 1) (2 * n - 2 ^ r) ↔ fromPrefix j.val ∨ j = a.succ := by
    rw [hs, mem_binaryExcedances_single_bit (by omega) (by omega)]
    rw [Fin.ext_iff]
    change (_ ∨ j.val = w + 1 - 1 - r) ↔ fromPrefix j.val ∨ j.val = a.val + 1
    have e₁ : w + 1 - (r + 2) = a.val := by dsimp [a]; omega
    have e₂ : w + 1 - 1 - r = a.val + 1 := by dsimp [a]; omega
    simp only [e₁, e₂, fromPrefix]
  have halfMem (j : Fin (w + 1)) :
      j ∈ binaryExcedances w n ↔ fromPrefix j.val ∨ j = a := by
    rw [hn', mem_binaryExcedances_single_bit (by omega) (by omega), Fin.ext_iff]
    have e : w - 1 - r = a.val := by dsimp [a]; omega
    simp only [fromPrefix, show w - (r + 1) = a.val by rfl, e]
  have removedMem (j : Fin (w + 1)) :
      j ∈ binaryExcedances w (n - 2 ^ r) ↔ fromPrefix j.val := by
    rw [hd, ← Nat.add_zero (2 ^ (r + 1) * h),
      mem_binaryExcedances_suffix (by omega) (by positivity)]
    simp [fromPrefix, a]
  let S := binaryExcedances (w + 1) (2 * n)
  have left : a.castSucc ∈ S := (evenMem _).mpr (Or.inr rfl)
  have right : a.succ ∉ S := by
    rw [show S = binaryExcedances (w + 1) (2 * n) by rfl, evenMem]
    exact fun h => h.elim (fun hp => (Nat.not_lt_of_ge (Nat.le_succ _) hp.1))
      (Ne.symm a.castSucc_lt_succ.ne)
  have swapped : Equiv.swap a.castSucc a.succ ⁻¹' S =
      binaryExcedances (w + 1) (2 * n - 2 ^ r) := by
    ext j
    change Equiv.swap a.castSucc a.succ j ∈ S ↔ _
    rw [show S = binaryExcedances (w + 1) (2 * n) by rfl, swappedMem]
    by_cases hl : j = a.castSucc
    · subst j
      rw [Equiv.swap_apply_left]
      exact iff_of_false right (fun h => h.elim (fun hp => (lt_irrefl _ hp.1))
        a.castSucc_lt_succ.ne)
    · by_cases hr : j = a.succ
      · subst j
        rw [Equiv.swap_apply_right]
        exact iff_of_true left (Or.inr rfl)
      · rw [Equiv.swap_apply_of_ne_of_ne hl hr, evenMem]
        simp [hl, hr]
  have deleteRight : a.succ.succAbove ⁻¹' S = binaryExcedances w n := by
    ext j
    change a.succ.succAbove j ∈ binaryExcedances (w + 1) (2 * n) ↔ _
    rw [halfMem]
    rcases lt_trichotomy j a with hj | rfl | hj
    · rw [Fin.succAbove_succ_of_le _ _ hj.le, evenMem]
      have hne : j.castSucc ≠ a.castSucc := (Fin.castSucc_lt_castSucc_iff.mpr hj).ne
      simp [hne, hj.ne]
    · rw [Fin.succAbove_succ_self, evenMem]
      simp
    · rw [Fin.succAbove_succ_of_lt _ _ hj, evenMem]
      have hne : j.succ ≠ a.castSucc := (Fin.castSucc_lt_succ_iff.mpr hj.le).ne.symm
      have hval : a.val < j.val := hj
      simp [hne, hj.ne.symm, fromPrefix, show ¬j.val + 1 < a.val by omega,
        show ¬j.val < a.val by omega]
  have deleteLeft : a.castSucc.succAbove ⁻¹' S = binaryExcedances w (n - 2 ^ r) := by
    ext j
    change a.castSucc.succAbove j ∈ binaryExcedances (w + 1) (2 * n) ↔ _
    rw [removedMem]
    by_cases hj : j < a
    · rw [Fin.succAbove_castSucc_of_lt _ _ hj, evenMem]
      have hne : j.castSucc ≠ a.castSucc := (Fin.castSucc_lt_castSucc_iff.mpr hj).ne
      simp [hne]
    · rw [Fin.succAbove_castSucc_of_le _ _ (le_of_not_gt hj), evenMem]
      have hval : a.val ≤ j.val := le_of_not_gt hj
      have hne : j.succ ≠ a.castSucc :=
        (Fin.castSucc_lt_succ_iff.mpr (le_of_not_gt hj)).ne.symm
      simp [hne, fromPrefix, show ¬j.val + 1 < a.val by omega, show ¬j.val < a.val by omega]
  unfold paddedCount
  change exactCount S = _
  rw [adjacentBA a S left right, swapped, deleteRight, deleteLeft]


private theorem paddedCount_eq_b (n : ℕ) :
    ∀ w : ℕ, n < 2 ^ w → (paddedCount w n : ℤ) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · simp [paddedCount_zero, b_zero]
    cases w with
    | zero => simp at hw; omega
    | succ w =>
      let q := n / 2
      have hq : q < n := Nat.div_lt_self hn (by decide)
      have hqw : q < 2 ^ w := by rw [pow_succ] at hw; dsimp [q]; omega
      by_cases he : n % 2 = 0
      · have hindex : n = 2 * q := by dsimp [q]; omega
        have hpos : 0 < q := by omega
        have hd : 0 < 2 ^ padicValNat 2 q := Nat.two_pow_pos _
        have hswap : 2 * q - 2 ^ padicValNat 2 q < n := by omega
        have hremoved : q - 2 ^ padicValNat 2 q < 2 ^ w :=
          (Nat.sub_le ..).trans_lt hqw
        have hswapWidth : 2 * q - 2 ^ padicValNat 2 q < 2 ^ (w + 1) :=
          hswap.trans hw
        rw [hindex, paddedCount_even hpos (hindex ▸ hw), b_even_index q hpos]
        push_cast
        rw [ih _ hswap _ hswapWidth, ih q hq _ hqw,
          ih _ ((Nat.sub_le ..).trans_lt hq) _ hremoved]
        ring
      · have hindex : n = 2 * q + 1 := by dsimp [q]; omega
        rw [hindex, paddedCount_odd, b_odd_index]
        exact ih q hq w hqw

/-- OEIS A329369 Conjecture 4 at every admissible padding width.
The sign uses the printed integer exponent, including the two upper columns. -/
theorem conjecture4 (m k w : ℕ) (hw : 2 ^ m * (2 * k + 1) < 2 ^ w) :
    (paddedCount w (2 ^ m * (2 * k + 1)) : ℚ) =
      ∑ i ∈ Finset.Icc 1 (wt k + 2),
        (i.factorial : ℚ) * (i : ℚ) ^ m * T k i *
          (-1 : ℚ) ^ ((wt k : ℤ) - (i : ℤ)) := by
  have h := congrArg (Int.castRingHom ℚ) (paddedCount_eq_b _ w hw)
  have h' : (paddedCount w (2 ^ m * (2 * k + 1)) : ℚ) =
      (b (2 ^ m * (2 * k + 1)) : ℚ) := by simpa using h
  exact h'.trans (b_factorial_sum m k)

#print axioms conjecture4

end
end D5.S3.Combinatorics.Permutation.KurkovA329369ConjectureFour
