/- GID: D5/S1/Words/Powers/WordPower
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:generic-list-bookkeeping)
   anchors: []
   digest: A finite word power is repeated concatenation, read modulo its period. -/

import Mathlib.Data.List.Basic

namespace D5.S1.Words.Powers

/-- The `k`-fold concatenation power of a finite word. -/
def wordPower {α : Type*} (k : Nat) (u : List α) : List α :=
  (List.replicate k u).flatten

@[simp] theorem wordPower_zero {α : Type*} (u : List α) : wordPower 0 u = [] := by
  simp [wordPower]

theorem wordPower_succ {α : Type*} (k : Nat) (u : List α) :
    wordPower (k + 1) u = u ++ wordPower k u := by
  simp [wordPower, List.replicate_succ]

@[simp] theorem wordPower_one {α : Type*} (u : List α) : wordPower 1 u = u := by
  simp [wordPower]

theorem length_wordPower {α : Type*} (k : Nat) (u : List α) :
    (wordPower k u).length = k * u.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [wordPower_succ, List.length_append, ih, Nat.succ_mul]; omega

/-- Every letter of a word power is the period letter at the reduced index. -/
theorem wordPower_getElem? {α : Type*} (k : Nat) (u : List α) (m : Nat)
    (hm : m < k * u.length) :
    (wordPower k u)[m]? = u[m % u.length]? := by
  induction k generalizing m with
  | zero => simp at hm
  | succ k ih =>
      rw [Nat.succ_mul] at hm
      rw [wordPower_succ]
      by_cases hlt : m < u.length
      · rw [List.getElem?_append_left hlt, Nat.mod_eq_of_lt hlt]
      · have hle : u.length ≤ m := Nat.le_of_not_lt hlt
        rw [List.getElem?_append_right hle]
        have hm' : m - u.length < k * u.length := by omega
        rw [ih _ hm', Nat.mod_eq_sub_mod hle]

/-- A word power repeats with its period wherever both indices are in range. -/
theorem wordPower_period_getElem? {α : Type*} (k : Nat) (u : List α) (m : Nat)
    (hm : m + u.length < k * u.length) :
    (wordPower k u)[m]? = (wordPower k u)[m + u.length]? := by
  have hm0 : m < k * u.length := by omega
  rw [wordPower_getElem? k u m hm0, wordPower_getElem? k u (m + u.length) hm,
    Nat.add_mod_right]

end D5.S1.Words.Powers
