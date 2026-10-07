/- GID: D5/S3/Combinatorics/Latin/LatinHLatinness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/LatinHLatinness
   mirror-E: none(waiver:literal-H-latinness)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Literal row and column bijectivity of the H square. -/

import D5.S3.Combinatorics.Latin.LatinHTransversals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinHLatinness

open D5.S3.Combinatorics.LatinHTransversals
open D5.S3.Combinatorics.LatinEulerianMultiples

set_option maxHeartbeats 3000000 in
/-- The literal H square is Latin for every integer parameter at least nine. -/
theorem literal_h_latinness (K : ℤ) (hK : 9 ≤ K) :
    let k := K.toNat
    let hk : 9 ≤ k := by omega
    IsLatin (order k) (square k hk) := by
  dsimp only
  let k := K.toNat
  have hk : 9 ≤ k := by dsimp [k]; omega
  have hkz : (9 : ℤ) ≤ (k : ℤ) := by omega
  have horder : (order k : ℤ) = 4 * (k : ℤ) := by simp [order]
  have residue_eq_cases (x y : ℤ)
      (hb : -2 * (order k : ℤ) < x - y ∧ x - y < 2 * (order k : ℤ))
      (h : residue k hk x = residue k hk y) :
      x - y = -(order k : ℤ) ∨ x - y = 0 ∨ x - y = order k := by
    have hx := Int.emod_nonneg x (by dsimp [order]; omega : (order k : ℤ) ≠ 0)
    have hy := Int.emod_nonneg y (by dsimp [order]; omega : (order k : ℤ) ≠ 0)
    have hmod : x % (order k : ℤ) = y % (order k : ℤ) := by
      have hv := congrArg (fun a : Fin (order k) => (a.val : ℤ)) h
      simpa only [residue, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] using hv
    have hzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod
    by_cases h0 : 0 ≤ x - y
    · by_cases hn : x - y < order k
      · rw [Int.emod_eq_of_lt h0 hn] at hzero
        exact Or.inr (Or.inl hzero)
      · have hs : 0 ≤ x - y - order k ∧ x - y - order k < order k := by omega
        have hz : (x - y - order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        exact Or.inr (Or.inr (by omega))
    · by_cases hn : -(order k : ℤ) ≤ x - y
      · have hs : 0 ≤ x - y + order k ∧ x - y + order k < order k := by omega
        have hz : (x - y + order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        exact Or.inl (by omega)
      · have hs : 0 ≤ x - y + 2 * order k ∧ x - y + 2 * order k < order k := by omega
        have hz : (x - y + 2 * order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        omega
  have row_injective : ∀ a : Fin (order k),
      Function.Injective (fun b => square k hk a b) := by
    intro a b c heq
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hdb : -4 ≤ delta k a b ∧ delta k a b ≤ 4 := by
      dsimp [delta]
      split_ifs <;> omega
    have hdc : -4 ≤ delta k a c ∧ delta k a c ≤ 4 := by
      dsimp [delta]
      split_ifs <;> omega
    have hbound :
        -2 * (order k : ℤ) <
          ((a.val : ℤ) + b.val + delta k a b) -
            ((a.val : ℤ) + c.val + delta k a c) ∧
        ((a.val : ℤ) + b.val + delta k a b) -
            ((a.val : ℤ) + c.val + delta k a c) < 2 * (order k : ℤ) := by
      clear heq
      have horder : (order k : ℤ) = 4 * (k : ℤ) := by simp [order]
      rw [horder]
      omega
    have hcases := residue_eq_cases
      ((a.val : ℤ) + b.val + delta k a b)
      ((a.val : ℤ) + c.val + delta k a c) hbound heq
    by_cases ha0 : a.val = 0 ∨ a.val = 5 ∨ a.val = 10
    · rcases ha0 with ha0 | ha0 | ha0
      all_goals simp [delta, ha0] at hcases
      all_goals split_ifs at hcases <;>
        rcases hcases with hminus | hzero | hplus <;>
        (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
    by_cases ha1 : a.val = 1 ∨ a.val = 6 ∨ a.val = 11
    · rcases ha1 with ha1 | ha1 | ha1
      all_goals simp [delta, ha1] at hcases
      all_goals split_ifs at hcases <;>
        rcases hcases with hminus | hzero | hplus <;>
        (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
    by_cases ha4 : a.val = 4 ∨ a.val = 9 ∨ a.val = 14
    · rcases ha4 with ha4 | ha4 | ha4
      all_goals simp [delta, ha4] at hcases
      all_goals split_ifs at hcases <;>
        rcases hcases with hminus | hzero | hplus <;>
        (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
    by_cases hbulk : 15 ≤ a.val ∧ a.val < order k - 21
    · have hlo := hbulk.1
      have hhi := hbulk.2
      by_cases ha3 : a.val % 4 = 3
      · simp [delta, ha0, ha1, ha4, hlo, hhi, ha3] at hcases
        split_ifs at hcases <;>
          rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
      by_cases ha1b : a.val % 4 = 1
      · simp [delta, ha0, ha1, ha4, hlo, hhi, ha3, ha1b] at hcases
        split_ifs at hcases <;>
          rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
      · have ha3' : a.val % 4 ≠ 3 := ha3
        have ha1b' : a.val % 4 ≠ 1 := ha1b
        simp [delta, ha0, ha1, ha4, hlo, hhi, ha3', ha1b'] at hcases
        rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
    have hdb0 : delta k a b = 0 := by
      dsimp [delta]
      split_ifs <;> omega
    have hdc0 : delta k a c = 0 := by
      dsimp [delta]
      split_ifs <;> omega
    rcases hcases with hminus | hzero | hplus
    · exfalso; omega
    · apply Fin.ext; omega
    · exfalso; omega
  have column_injective : ∀ b : Fin (order k),
      Function.Injective (fun a => square k hk a b) := by
    intro b a c heq
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hdb : -4 ≤ delta k a b ∧ delta k a b ≤ 4 := by
      dsimp [delta]
      split_ifs <;> omega
    have hdc : -4 ≤ delta k c b ∧ delta k c b ≤ 4 := by
      dsimp [delta]
      split_ifs <;> omega
    have hbound :
        -2 * (order k : ℤ) <
          ((a.val : ℤ) + b.val + delta k a b) -
            ((c.val : ℤ) + b.val + delta k c b) ∧
        ((a.val : ℤ) + b.val + delta k a b) -
            ((c.val : ℤ) + b.val + delta k c b) < 2 * (order k : ℤ) := by
      clear heq
      rw [horder]
      omega
    have hcases := residue_eq_cases
      ((a.val : ℤ) + b.val + delta k a b)
      ((c.val : ℤ) + b.val + delta k c b) hbound heq
    by_cases hb1 : b.val % 4 = 1
    · by_cases hbq1 : b.val = 1
      · simp [delta, hb1, hbq1] at hcases
        split_ifs at hcases <;>
          rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
      by_cases hbq5 : b.val = 5
      · simp [delta, hb1, hbq1, hbq5] at hcases
        split_ifs at hcases <;>
          rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
      by_cases hbq9 : b.val = 9
      · simp [delta, hb1, hbq1, hbq5, hbq9] at hcases
        split_ifs at hcases <;>
          rcases hcases with hminus | hzero | hplus <;>
          (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
      have hda : delta k a b =
          if a.val = 0 ∨ a.val = 5 ∨ a.val = 10 then 4
          else if a.val = 4 ∨ a.val = 9 ∨ a.val = 14 then -4 else 0 := by
        dsimp [delta]
        split_ifs <;> omega
      have hdc' : delta k c b =
          if c.val = 0 ∨ c.val = 5 ∨ c.val = 10 then 4
          else if c.val = 4 ∨ c.val = 9 ∨ c.val = 14 then -4 else 0 := by
        dsimp [delta]
        split_ifs <;> omega
      rw [hda, hdc'] at hcases
      split_ifs at hcases <;>
        rcases hcases with hminus | hzero | hplus <;>
        (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
    · have hbne1 : b.val ≠ 1 := by omega
      have hbne5 : b.val ≠ 5 := by omega
      have hbne9 : b.val ≠ 9 := by omega
      have hdelta (x : Fin (order k)) :
          delta k x b =
            if (x.val = 0 ∨ x.val = 5 ∨ x.val = 10) ∧
                1 ≤ (b.val : ℤ) - 4 * (x.val : ℤ) / 5 ∧
                (b.val : ℤ) - 4 * (x.val : ℤ) / 5 ≤ 4 then 1
            else if (x.val = 1 ∨ x.val = 6 ∨ x.val = 11) ∧
                2 ≤ (b.val : ℤ) - 4 * ((x.val : ℤ) - 1) / 5 ∧
                (b.val : ℤ) - 4 * ((x.val : ℤ) - 1) / 5 ≤ 4 then -1
            else if 15 ≤ x.val ∧ x.val < order k - 21 ∧
                x.val % 4 = 3 ∧ b.val % 2 = 0 then 2
            else if 15 ≤ x.val ∧ x.val < order k - 21 ∧
                x.val % 4 = 1 ∧ b.val % 2 = 0 then -2 else 0 := by
        simp [delta, hb1, hbne1, hbne5, hbne9]
      rw [hdelta a, hdelta c] at hcases
      split_ifs at hcases <;>
        rcases hcases with hminus | hzero | hplus <;>
        (try { apply Fin.ext; omega }) <;> (try { exfalso; omega })
  constructor
  · intro a
    exact (Finite.injective_iff_bijective).mp (row_injective a)
  · intro b
    exact (Finite.injective_iff_bijective).mp (column_injective b)

end D5.S3.Combinatorics.LatinHLatinness
