/- GID: D5/S1/Digit/KurkovRunAlternatingCount
   generality: G
   mirror-B: D5/B/S1/Digit/KurkovRunAlternatingCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Alternating overlapping binary one-block counts equal A329320 for every natural. -/

import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Only Kurkov's October 13, 2021 formula in OEIS A239907 is considered here.
Bit indices start at zero, occurrences overlap, and bits beyond `n.size` are zero.
The valuation expression for A329320 uses the supplied positive-index
characterization of A035263; its morphic definition is not formalized here.
The alternating sum and subtraction are in ℤ; `n / 2 ^ i` is natural division.
Both ranges are empty at zero, giving 0 = 0.

The definitions range over all naturals and the theorem is an unbounded symbolic
identity. No declaration is a bounded enumeration, checker, numeric reduction,
or certified finite instance, so `utility: none` applies throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.KurkovRunAlternatingCount

open Finset

/-- Number of overlapping occurrences of 1^k in the binary expansion of n (A239907's cn),
indexed by the low bit of each occurrence. Only positive k enter the alternating sum. -/
def cn (n k : ℕ) : ℕ :=
  ((range n.size).filter fun i => ∀ j < k, n.testBit (i + j) = true).card

/-- A329320, using 1 − A035263(m) = [v_2(m) odd] for positive m.
The range is empty at n = 0. -/
noncomputable def b (n : ℕ) : ℕ :=
  ((range n.size).filter fun i => Odd (padicValNat 2 (n / 2 ^ i + 1))).card

/-- The A239907 conjecture attributed to Mikhail Kurkov, Oct 13 2021,
using overlapping occurrences and the supplied valuation formula for A329320. -/
theorem result (n : ℕ) :
    (n : ℤ) - ∑ k ∈ Finset.Icc 1 n.size, (-1 : ℤ) ^ (k + 1) * (cn n k : ℤ) =
      (n : ℤ) - (b n : ℤ) := by
  classical
  -- All lower bits are one exactly when adding one is divisible by 2^k.
  have bits (m k : ℕ) :
      (∀ j < k, m.testBit j = true) ↔ k ≤ padicValNat 2 (m + 1) := by
    rw [← padicValNat_dvd_iff_le (by omega : m + 1 ≠ 0)]
    rw [← Nat.mod_eq_sub_iff (by omega : 0 < 1) (Nat.two_pow_pos k)]
    rw [Nat.eq_iff_testBit_eq]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    constructor
    · intro h j
      by_cases hj : j < k <;> simp [hj, h]
    · intro h j hj
      simpa [hj] using h j
  let t (i : ℕ) := padicValNat 2 (n / 2 ^ i + 1)
  have run (i k : ℕ) :
      (∀ j < k, n.testBit (i + j) = true) ↔ k ≤ t i := by
    simpa only [t, Nat.testBit_div_two_pow, Nat.add_comm] using bits (n / 2 ^ i) k
  -- This proves that truncation at the digit length discards only zero counts.
  have tail (k : ℕ) (hk : n.size < k) : cn n k = 0 := by
    simp only [cn, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range]
    intro i hi hall
    have hb := hall n.size hk
    have hf : n.testBit (i + n.size) = false :=
      Nat.testBit_lt_two_pow ((Nat.lt_size_self n).trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : n.size ≤ i + n.size)))
    simp [hf] at hb
  have bound (i : ℕ) (hi : i ∈ range n.size) : t i ≤ n.size := by
    by_contra h
    have hz := tail (t i) (by omega)
    have hm : i ∈ (range n.size).filter (fun q => ∀ j < t i, n.testBit (q + j) = true) :=
      Finset.mem_filter.mpr ⟨hi, (run i (t i)).mpr le_rfl⟩
    have hp : 0 < cn n (t i) := Finset.card_pos.mpr ⟨i, hm⟩
    omega
  have alternating (r : ℕ) :
      (∑ k ∈ Icc 1 r, (-1 : ℤ) ^ (k + 1)) = if Odd r then 1 else 0 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right]
    have he (k : ℕ) : (-1 : ℤ) ^ (1 + k + 1) = (-1 : ℤ) ^ k := by
      rw [show 1 + k + 1 = k + 2 by omega, pow_add]
      norm_num
    simp_rw [he]
    rw [neg_one_geom_sum]
    by_cases h : Even r <;> simp [← Nat.not_even_iff_odd, h]
  apply congrArg (fun z : ℤ => (n : ℤ) - z)
  calc
    (∑ k ∈ Icc 1 n.size, (-1 : ℤ) ^ (k + 1) * (cn n k : ℤ)) =
        ∑ k ∈ Icc 1 n.size, ∑ i ∈ range n.size,
          if k ≤ t i then (-1 : ℤ) ^ (k + 1) else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [cn, ← sum_boole]
      simp_rw [mul_sum, mul_ite, mul_one, mul_zero, run]
    _ = ∑ i ∈ range n.size, ∑ k ∈ Icc 1 n.size,
          if k ≤ t i then (-1 : ℤ) ^ (k + 1) else 0 := sum_comm
    _ = ∑ i ∈ range n.size, if Odd (t i) then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter]
      have hs : (Icc 1 n.size).filter (fun k => k ≤ t i) = Icc 1 (t i) := by
        ext k
        simp only [mem_filter, mem_Icc]
        have hb := bound i hi
        omega
      rw [hs, alternating]
    _ = (b n : ℤ) := by
      simpa only [b, t] using
        (sum_boole (fun i => Odd (padicValNat 2 (n / 2 ^ i + 1))) (range n.size) :
          (∑ i ∈ range n.size, if Odd (padicValNat 2 (n / 2 ^ i + 1)) then (1 : ℤ) else 0) = _)

end D5.S1.Digit.KurkovRunAlternatingCount
