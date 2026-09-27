/- GID: D5/S3/Combinatorics/LatinEulerianShiftCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianShiftCount
   mirror-E: none(waiver:direct-residue-comparison-proof-for-shifted-Latin-squares)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: Swapping zero and one changes exactly the two exceptional modular-shift comparisons. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

/-- Exchange the values zero and one in an ordinary residue representative. -/
def swap01 (x : ℕ) : ℕ := if x = 0 then 1 else if x = 1 then 0 else x

theorem shifted_comparison {n d x : ℕ} (hn : 3 ≤ n)
    (hd0 : 0 < d) (hdn : d < n) (hxn : x < n) :
    swap01 x < swap01 ((x + d) % n) ↔
      (x < n - d ∧ ¬ (d = 1 ∧ x = 0)) ∨ (d = n - 1 ∧ x = 1) := by
  by_cases hwrap : x + d < n
  · have hmod : (x + d) % n = x + d := Nat.mod_eq_of_lt hwrap
    rw [hmod]
    have hx : x < n - d := by omega
    unfold swap01
    split_ifs <;> omega
  · have hsmall : x + d - n < n := by omega
    have hmod : (x + d) % n = x + d - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsmall]
    rw [hmod]
    have hx : ¬ x < n - d := by omega
    unfold swap01
    split_ifs <;> omega

/-- The number of ascending residue pairs after swapping the two least symbols. -/
def shiftedAscents (n d : ℕ) : ℕ :=
  ((Finset.range n).filter (fun x => swap01 x < swap01 ((x + d) % n))).card

theorem shifted_ascent_count {n d : ℕ} (hn : 3 ≤ n)
    (hd0 : 0 < d) (hdn : d < n) :
    shiftedAscents n d + (if d = 1 then 1 else 0) =
      (n - d) + (if d = n - 1 then 1 else 0) := by
  classical
  by_cases hfirst : d = 1
  · have hlast : d ≠ n - 1 := by omega
    have hset : (Finset.range n).filter
        (fun x => swap01 x < swap01 ((x + d) % n)) =
        (Finset.range (n - 1)).erase 0 := by
      ext x
      by_cases hx : x < n
      · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, hx, true_and]
        rw [shifted_comparison hn hd0 hdn hx]
        simp [hfirst]
        omega
      · have hnx : ¬ x < n - 1 := by omega
        simp [Finset.mem_filter, Finset.mem_erase, hx, hnx]
    rw [shiftedAscents, hset, Finset.card_erase_of_mem (by simp; omega)]
    simp only [if_pos hfirst, if_neg hlast, Finset.card_range]
    rw [hfirst]
    omega
  by_cases hlast : d = n - 1
  · have hset : (Finset.range n).filter
        (fun x => swap01 x < swap01 ((x + d) % n)) =
        insert 1 (Finset.range 1) := by
      ext x
      by_cases hx : x < n
      · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, hx, true_and]
        rw [shifted_comparison hn hd0 hdn hx]
        simp [hlast]
        omega
      · have hx1 : x ≠ 1 := by omega
        have hx0 : x ≠ 0 := by omega
        simp [Finset.mem_filter, hx, hx0, hx1]
    have hcard : (insert 1 (Finset.range 1) : Finset ℕ).card = 2 := by decide
    rw [shiftedAscents, hset, hcard]
    simp only [if_neg hfirst, if_pos hlast]
    rw [hlast]
    omega
  · have hset : (Finset.range n).filter
        (fun x => swap01 x < swap01 ((x + d) % n)) =
        Finset.range (n - d) := by
      ext x
      by_cases hx : x < n
      · simp only [Finset.mem_filter, Finset.mem_range, hx, true_and]
        rw [shifted_comparison hn hd0 hdn hx]
        simp [hfirst, hlast]
      · have hnx : ¬ x < n - d := by omega
        simp [Finset.mem_filter, hx, hnx]
    simp [shiftedAscents, hset, hfirst, hlast]
end D5.S3.Combinatorics.LatinEulerianMultiples
