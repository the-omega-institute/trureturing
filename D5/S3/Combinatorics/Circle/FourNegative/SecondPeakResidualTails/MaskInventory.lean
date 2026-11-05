import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits
import D5.S3.Combinatorics.Circle.ThreeBitSource
import Mathlib.Tactic

/-! Exact binary inventories, consuming the original public complement proof. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open scoped BigOperators

def bits (m : ℕ) : Finset ℕ := m.bitIndices.toFinset

@[simp] theorem mem_bits (e m : ℕ) : e ∈ bits m ↔ m.testBit e = true := by
  simp only [bits, List.mem_toFinset, Nat.mem_bitIndices]

@[simp] theorem bits_zero : bits 0 = ∅ := by simp [bits]

/-- The inventory records occurrences, including uniqueness of their bank.
Its last field is a statement about bit supports, not an integer sum. -/
structure MaskInventory (width : ℕ) (m : Fin 4 → ℕ) : Prop where
  capacity : ∀ bank, m bank < 2 ^ width
  unique : ∀ e i j, e ∈ bits (m i) → e ∈ bits (m j) → i = j
  complete : ∀ e, e < width ↔ ∃ bank, e ∈ bits (m bank)

/-- Only the literal high-bit tables use finite bit positions.  Capacity and
the public bit_below theorem extend them to *all* natural bit positions. -/
theorem inventory_of_finite_bits (width : ℕ) (m : Fin 4 → ℕ)
    (hcap : ∀ bank, m bank < 2 ^ width)
    (hunique : ∀ e : Fin width, ∀ i j : Fin 4,
      (m i).testBit e.val = true → (m j).testBit e.val = true → i = j)
    (hcomplete : ∀ e : Fin width, ∃ bank : Fin 4, (m bank).testBit e.val = true) :
    MaskInventory width m := by
  refine ⟨hcap, ?_, ?_⟩
  · intro e i j hi hj
    have he := SecondPeakHighD.bit_below (m i) width e (hcap i) ((mem_bits _ _).mp hi)
    exact hunique ⟨e,he⟩ i j ((mem_bits _ _).mp hi) ((mem_bits _ _).mp hj)
  · intro e
    constructor
    · intro he
      obtain ⟨bank,hb⟩ := hcomplete ⟨e,he⟩
      exact ⟨bank,(mem_bits _ _).mpr hb⟩
    · rintro ⟨bank,hb⟩
      exact SecondPeakHighD.bit_below (m bank) width e (hcap bank) ((mem_bits _ _).mp hb)

theorem MaskInventory.disjoint {width : ℕ} {m : Fin 4 → ℕ}
    (h : MaskInventory width m) (i j : Fin 4) (hij : i ≠ j) :
    Disjoint (bits (m i)) (bits (m j)) := by
  exact Finset.disjoint_left.mpr (fun e hi hj => hij (h.unique e i j hi hj))

theorem MaskInventory.full {width : ℕ} {m : Fin 4 → ℕ}
    (h : MaskInventory width m) :
    bits (m 0) ∪ bits (m 1) ∪ bits (m 2) ∪ bits (m 3) =
      Finset.range width := by
  ext e
  simp only [Finset.mem_union, Finset.mem_range]
  rw [h.complete]
  constructor
  · rintro (((he | he) | he) | he)
    · exact ⟨0, he⟩
    · exact ⟨1, he⟩
    · exact ⟨2, he⟩
    · exact ⟨3, he⟩
  · rintro ⟨bank, he⟩
    fin_cases bank <;> tauto

/-- Place an exact complementary pair in two distinct banks. -/
theorem inventory_pair (width m n : ℕ) (hsum : m + n = 2 ^ width - 1)
    (i j : Fin 4) (hij : i ≠ j) :
    MaskInventory width (fun bank =>
      if bank = i then m else if bank = j then n else 0) := by
  classical
  have hc := D5.S3.Combinatorics.Circle.ThreeBitSource.mask_complement
    width m n hsum
  have hp := Nat.two_pow_pos width
  have hm : m < 2 ^ width := by omega
  have hn : n < 2 ^ width := by omega
  have hmn : Disjoint (bits m) (bits n) := hc.1
  have hfull : bits m ∪ bits n = Finset.range width := hc.2
  constructor
  · intro bank
    split_ifs <;> assumption
  · intro e r s hr hs
    by_cases hri : r = i
    · subst r
      simp only [if_pos rfl] at hr
      by_cases hsi : s = i
      · exact hsi.symm
      · by_cases hsj : s = j
        · subst s
          simp only [if_neg hij.symm, if_pos rfl] at hs
          exact False.elim (Finset.disjoint_left.mp hmn hr hs)
        · simp [hsi, hsj] at hs
    · by_cases hrj : r = j
      · subst r
        simp only [if_neg hij.symm, if_pos rfl] at hr
        by_cases hsj : s = j
        · exact hsj.symm
        · by_cases hsi : s = i
          · subst s
            simp only [if_pos rfl] at hs
            exact False.elim (Finset.disjoint_left.mp hmn hs hr)
          · simp [hsi, hsj] at hs
      · simp [hri, hrj] at hr
  · intro e
    have he : e < width ↔ e ∈ bits m ∨ e ∈ bits n := by
      rw [← Finset.mem_range, ← hfull, Finset.mem_union]
    rw [he]
    constructor
    · rintro (hm' | hn')
      · exact ⟨i, by simpa using hm'⟩
      · exact ⟨j, by simpa [hij.symm] using hn'⟩
    · rintro ⟨bank, hb⟩
      by_cases hbi : bank = i
      · exact Or.inl (by simpa [hbi] using hb)
      · by_cases hbj : bank = j
        · exact Or.inr (by simpa [hbi, hbj] using hb)
        · simp [hbi, hbj] at hb

theorem inventory_02 (width m n : ℕ) (hsum : m + n = 2 ^ width - 1) :
    MaskInventory width ![m, 0, n, 0] := by
  have heq : (fun bank : Fin 4 =>
      if bank = 0 then m else if bank = 2 then n else 0) = ![m, 0, n, 0] := by
    ext bank; fin_cases bank <;> simp
  simpa only [heq] using inventory_pair width m n hsum 0 2 (by decide)

theorem inventory_01 (width m n : ℕ) (hsum : m + n = 2 ^ width - 1) :
    MaskInventory width ![m, n, 0, 0] := by
  have heq : (fun bank : Fin 4 =>
      if bank = 0 then m else if bank = 1 then n else 0) = ![m, n, 0, 0] := by
    ext bank; fin_cases bank <;> simp
  simpa only [heq] using inventory_pair width m n hsum 0 1 (by decide)

theorem inventory_03 (width m n : ℕ) (hsum : m + n = 2 ^ width - 1) :
    MaskInventory width ![m, 0, 0, n] := by
  have heq : (fun bank : Fin 4 =>
      if bank = 0 then m else if bank = 3 then n else 0) = ![m, 0, 0, n] := by
    ext bank; fin_cases bank <;> simp
  simpa only [heq] using inventory_pair width m n hsum 0 3 (by decide)

theorem inventory_13 (width m n : ℕ) (hsum : m + n = 2 ^ width - 1) :
    MaskInventory width ![0, m, 0, n] := by
  have heq : (fun bank : Fin 4 =>
      if bank = 1 then m else if bank = 3 then n else 0) = ![0, m, 0, n] := by
    ext bank; fin_cases bank <;> simp
  simpa only [heq] using inventory_pair width m n hsum 1 3 (by decide)

/-- A high mask and a low mask occupy separate binary blocks in each bank. -/
theorem inventory_blocks (loWidth hiWidth : ℕ) (lo hi : Fin 4 → ℕ)
    (hl : MaskInventory loWidth lo) (hh : MaskInventory hiWidth hi) :
    MaskInventory (loWidth + hiWidth)
      (fun bank => 2 ^ loWidth * hi bank + lo bank) := by
  have hbit (bank : Fin 4) (e : ℕ) :
      (2 ^ loWidth * hi bank + lo bank).testBit e =
        if e < loWidth then (lo bank).testBit e
        else (hi bank).testBit (e - loWidth) :=
    Nat.testBit_two_pow_mul_add (hi bank) (hl.capacity bank) e
  constructor
  · intro bank
    calc
      2 ^ loWidth * hi bank + lo bank <
          2 ^ loWidth * hi bank + 2 ^ loWidth :=
        Nat.add_lt_add_left (hl.capacity bank) _
      _ = 2 ^ loWidth * (hi bank + 1) := by ring
      _ ≤ 2 ^ loWidth * 2 ^ hiWidth :=
        Nat.mul_le_mul_left _ (by have := hh.capacity bank; omega)
      _ = 2 ^ (loWidth + hiWidth) := (pow_add _ _ _).symm
  · intro e i j hi' hj'
    simp only [mem_bits, hbit] at hi' hj'
    by_cases he : e < loWidth
    · simp only [he, ite_true] at hi' hj'
      exact hl.unique e i j (by simpa using hi') (by simpa using hj')
    · simp only [he, ite_false] at hi' hj'
      exact hh.unique (e - loWidth) i j (by simpa using hi') (by simpa using hj')
  · intro e
    by_cases he : e < loWidth
    · constructor
      · intro _
        obtain ⟨bank, hb⟩ := (hl.complete e).mp he
        exact ⟨bank, by simpa only [mem_bits, hbit, he, ite_true] using hb⟩
      · intro _; omega
    · have heq : e < loWidth + hiWidth ↔ e - loWidth < hiWidth := by omega
      rw [heq, hh.complete]
      constructor <;> rintro ⟨bank, hb⟩ <;>
        exact ⟨bank, by simpa only [mem_bits, hbit, he, ite_false] using hb⟩

/-- This is the dyadic premise used by *both* low transfers.  In particular,
no theorem here replaces 2^ell by an arbitrary positive integer. -/
theorem reserve_below (e ell R : ℕ) (hR : R < 2 ^ e) :
    R * 2 ^ ell < 2 ^ (e + ell) ∧
      SecondPeakHighD.Submask (R * 2 ^ ell) (2 ^ (e + ell) - 1) := by
  have hcap : R * 2 ^ ell < 2 ^ (e + ell) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hR (Nat.two_pow_pos ell)
  refine ⟨hcap, ?_⟩
  simpa only [Nat.mul_one] using
    SecondPeakHighD.submask_predecessor (e + ell) 1 (R * 2 ^ ell) (by decide) hcap

theorem reserve_inventory (e ell R : ℕ) (hR : R < 2 ^ e) :
    MaskInventory (e + ell)
      ![0, R * 2 ^ ell, 0, 2 ^ (e + ell) - 1 - R * 2 ^ ell] := by
  have hr := reserve_below e ell R hR
  have hle := SecondPeakHighD.submask_le (R * 2 ^ ell) (2 ^ (e + ell) - 1) hr.2
  have hsum : R * 2 ^ ell + (2 ^ (e + ell) - 1 - R * 2 ^ ell) =
      2 ^ (e + ell) - 1 := Nat.add_sub_of_le hle
  exact inventory_13 (e + ell) (R * 2 ^ ell)
    (2 ^ (e + ell) - 1 - R * 2 ^ ell) hsum

def wMasks (e ell R : ℕ) (p : Fin 4 → ℕ) : Fin 4 → ℕ :=
  let q := 2 ^ e * 2 ^ ell
  ![p 0 * q, p 1 * q + R * 2 ^ ell, p 2 * q,
    p 3 * q + q - 1 - R * 2 ^ ell]

theorem w_inventory (e ell R hiWidth : ℕ) (p : Fin 4 → ℕ)
    (hR : R < 2 ^ e) (hp : MaskInventory hiWidth p) :
    MaskInventory (e + ell + hiWidth) (wMasks e ell R p) := by
  have hq : 2 ^ e * 2 ^ ell = (2 : ℕ) ^ (e + ell) := (pow_add _ _ _).symm
  have hr := (reserve_below e ell R hR).1
  have hpos := Nat.two_pow_pos (e + ell)
  have heq : (fun bank => 2 ^ (e + ell) * p bank +
      (![0, R * 2 ^ ell, 0, 2 ^ (e + ell) - 1 - R * 2 ^ ell] : Fin 4 → ℕ) bank) =
      wMasks e ell R p := by
    ext bank
    fin_cases bank <;> simp [wMasks, hq, Nat.mul_comm]
    omega
  simpa only [heq] using inventory_blocks (e + ell) hiWidth
    ![0, R * 2 ^ ell, 0, 2 ^ (e + ell) - 1 - R * 2 ^ ell] p
    (reserve_inventory e ell R hR) hp

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
