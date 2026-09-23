/- GID: D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first high-digit change reconstructs a p-adic residue. -/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.PadicHighDigitReconstruction

/-- The digit at depth `k` of an actual p-adic integer. -/
noncomputable def highDigit (p k : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℕ :=
  (PadicInt.toZModPow (k + 1) x).val / p ^ k

/-- Exactly `p ^ k` successive readings along the adding-one orbit. -/
noncomputable def word (p k : ℕ) [Fact p.Prime] (x : ℤ_[p]) : Fin (p ^ k) → ℕ :=
  fun n => highDigit p k (x + (n.val : ℤ_[p]))

/-- The first index differing from the initial reading, or the word length
when every reading is unchanged. -/
def firstChange (P : ℕ) (hP : 0 < P) (w : Fin P → ℕ) : ℕ :=
  let changes := Finset.univ.filter fun n => w n ≠ w ⟨0, hP⟩
  if h : changes.Nonempty then (changes.min' h).val else P

/-- Recover the leading block and the remainder from the first change. -/
def decode (P : ℕ) (hP : 0 < P) (w : Fin P → ℕ) : ℕ :=
  w ⟨0, hP⟩ * P + (P - firstChange P hP w)

/-- The timed high-digit word determines precisely the residue modulo `p^(k+1)`.
Its first change is `P-r`, with the sentinel `P` exactly when `r=0`.
The carry formula and change criterion include the wrap from `p-1` to zero. -/
theorem result (p k : ℕ) [Fact p.Prime] :
    let P := p ^ k
    let hP : 0 < P := pow_pos (Fact.out : p.Prime).pos k
    (∀ x : ℤ_[p],
      let z := (PadicInt.toZModPow (k + 1) x).val
      let b := z / P
      let r := z % P
      b < p ∧ r < P ∧ z = b * P + r ∧
      word p k x ⟨0, hP⟩ = b ∧
      (∀ n : Fin P, word p k x n = (b + (r + n.val) / P) % p ∧
        (r + n.val) / P ≤ 1) ∧
      (∀ n : Fin P, word p k x n ≠ b ↔ P - r ≤ n.val ∧ r ≠ 0) ∧
      firstChange P hP (word p k x) = P - r ∧
      (firstChange P hP (word p k x) = P ↔ r = 0) ∧
      decode P hP (word p k x) = z) ∧
    (∀ x y : ℤ_[p], word p k x = word p k y ↔
      PadicInt.toZModPow (k + 1) x = PadicInt.toZModPow (k + 1) y) := by
  let P := p ^ k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hP : 0 < P := pow_pos (Fact.out : p.Prime).pos k
  have hpow : p ^ (k + 1) = P * p := pow_succ p k
  have hstate (x : ℤ_[p]) :
      let z := (PadicInt.toZModPow (k + 1) x).val
      let b := z / P
      let r := z % P
      b < p ∧ r < P ∧ z = b * P + r ∧
      word p k x ⟨0, hP⟩ = b ∧
      (∀ n : Fin P, word p k x n = (b + (r + n.val) / P) % p ∧
        (r + n.val) / P ≤ 1) ∧
      (∀ n : Fin P, word p k x n ≠ b ↔ P - r ≤ n.val ∧ r ≠ 0) ∧
      firstChange P hP (word p k x) = P - r ∧
      (firstChange P hP (word p k x) = P ↔ r = 0) ∧
      decode P hP (word p k x) = z := by
    let z := (PadicInt.toZModPow (k + 1) x).val
    let b := z / P
    let r := z % P
    have hz : z < P * p := by
      simpa only [z, hpow] using ZMod.val_lt (PadicInt.toZModPow (k + 1) x)
    have hb : b < p := (Nat.div_lt_iff_lt_mul hP).2 (by simpa [Nat.mul_comm] using hz)
    have hr : r < P := Nat.mod_lt z hP
    have hzsplit : z = b * P + r := (Nat.div_add_mod' z P).symm
    have hzero : word p k x ⟨0, hP⟩ = b := by
      simp only [word, Nat.cast_zero, add_zero, highDigit, b, z, P]
    have hcarry (n : Fin P) :
        word p k x n = (b + (r + n.val) / P) % p := by
      have hn : n.val < p ^ (k + 1) := by
        rw [hpow]
        exact n.isLt.trans_le (Nat.le_mul_of_pos_right P (by omega))
      change (PadicInt.toZModPow (k + 1) (x + (n.val : ℤ_[p]))).val / P = _
      rw [map_add, map_natCast, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
      change (z + n.val) % p ^ (k + 1) / P = _
      rw [hpow, Nat.mod_mul_right_div_self]
      rw [hzsplit, Nat.add_assoc, Nat.mul_comm b P, Nat.mul_add_div hP]
    have hquot (n : Fin P) :
        (r + n.val) / P = if r + n.val < P then 0 else 1 := by
      split
      · exact Nat.div_eq_of_lt ‹_›
      · apply (Nat.div_eq_iff hP).2
        simp only [Nat.one_mul]
        omega
    have hwrap : (b + 1) % p ≠ b := by
      by_cases h : b + 1 < p
      · rw [Nat.mod_eq_of_lt h]
        omega
      · have heq : b + 1 = p := by omega
        rw [heq, Nat.mod_self]
        omega
    have hchange (n : Fin P) :
        word p k x n ≠ b ↔ P - r ≤ n.val ∧ r ≠ 0 := by
      rw [hcarry, hquot]
      split
      · simp only [Nat.add_zero, Nat.mod_eq_of_lt hb, ne_eq, not_true_eq_false,
          false_iff, not_and, not_not]
        omega
      · rw [iff_true_intro hwrap]
        constructor
        · intro _
          refine ⟨Nat.sub_le_iff_le_add.mpr (by omega), ?_⟩
          intro hr0
          have hn := n.isLt
          omega
        · intro _
          trivial
    have hfirst : firstChange P hP (word p k x) = P - r := by
      let changes := Finset.univ.filter fun n : Fin P =>
        word p k x n ≠ word p k x ⟨0, hP⟩
      have hmem (n : Fin P) : n ∈ changes ↔ P - r ≤ n.val ∧ r ≠ 0 := by
        simp only [changes, Finset.mem_filter, Finset.mem_univ, true_and, hzero, hchange]
      change (if h : changes.Nonempty then (changes.min' h).val else P) = P - r
      by_cases hr0 : r = 0
      · have hempty : ¬ changes.Nonempty := by
          rintro ⟨n, hn⟩
          exact ((hmem n).1 hn).2 hr0
        rw [dif_neg hempty, hr0, Nat.sub_zero]
      · have ht : P - r < P := by omega
        let t : Fin P := ⟨P - r, ht⟩
        have htmem : t ∈ changes := (hmem t).2 ⟨le_rfl, hr0⟩
        have hne : changes.Nonempty := ⟨t, htmem⟩
        rw [dif_pos hne]
        have hmin : changes.min' hne = t := by
          apply (Finset.min'_eq_iff _ _ _).2
          exact ⟨htmem, fun n hn => (hmem n).1 hn |>.1⟩
        exact congrArg Fin.val hmin
    have hdecode : decode P hP (word p k x) = z := by
      unfold decode
      rw [hzero, hfirst, Nat.sub_sub_self hr.le]
      exact hzsplit.symm
    have hconstant : firstChange P hP (word p k x) = P ↔ r = 0 := by
      rw [hfirst]
      constructor
      · intro h
        have hsum := Nat.sub_add_cancel hr.le
        rw [h] at hsum
        omega
      · intro h
        rw [h, Nat.sub_zero]
    exact ⟨hb, hr, hzsplit, hzero, fun n => ⟨hcarry n, by rw [hquot]; split <;> omega⟩,
      hchange, hfirst, hconstant, hdecode⟩
  refine ⟨hstate, ?_⟩
  intro x y
  constructor
  · intro hw
    apply ZMod.val_injective
    have hx := (hstate x).2.2.2.2.2.2.2.2
    have hy := (hstate y).2.2.2.2.2.2.2.2
    rw [← hx, ← hy, hw]
  · intro hq
    funext n
    simp only [word, highDigit, map_add, map_natCast, hq]

#print axioms result

end D5.S3.Observer.ArithmeticTomography.PadicHighDigitReconstruction
