/- GID: D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The unique positive Pythagorean triple of three A090467 terms is three-four-five. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.MarcusPythagoreanNonpolygonalTriple

/-- The `m`-th `k`-gonal number, in a subtraction-free natural-number form. -/
def polygonal (k m : Nat) : Nat :=
  m + (k - 2) * Nat.choose m 2

example {k m : Nat} (hk : 2 < k) (hm : 2 < m) :
    polygonal k m = 1 + k * m * (m - 1) / 2 - (m - 1) ^ 2 := by
  have heven : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have hc : 2 * Nat.choose m 2 = m * (m - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' heven
  have hdiv : k * m * (m - 1) / 2 = k * Nat.choose m 2 := by
    rw [mul_assoc, Nat.choose_two_right, Nat.mul_div_assoc k heven]
  have hk' : k = k - 2 + 2 := by omega
  have hm' : m = m - 1 + 1 := by omega
  have hsum :
      m + (k - 2) * Nat.choose m 2 + (m - 1) ^ 2 =
        1 + k * Nat.choose m 2 := by
    nlinarith
  simp only [polygonal]
  rw [hdiv]
  omega

/-- Membership in OEIS A090467: no polygonal representation of order and index above two. -/
def nonpolygonal (n : Nat) : Prop :=
  ¬ ∃ k : Nat, 2 < k ∧ ∃ m : Nat, 2 < m ∧ n = polygonal k m

/-- The exact unordered-leg reading of Michel Marcus's A344083 conjecture. -/
def claim : Prop :=
  (nonpolygonal 3 ∧ nonpolygonal 4 ∧ nonpolygonal 5 ∧ 3 ^ 2 + 4 ^ 2 = 5 ^ 2) ∧
    ∀ x y z : ℕ, 0 < x → 0 < y → x ^ 2 + y ^ 2 = z ^ 2 →
      nonpolygonal x → nonpolygonal y → nonpolygonal z → ({x, y} : Finset ℕ) = {3, 4} ∧ z = 5

private theorem eq_three_of_nonpolygonal_of_three_dvd
    {n : Nat} (hn : 0 < n) (hnp : nonpolygonal n) (hd : 3 ∣ n) : n = 3 := by
  obtain ⟨t, rfl⟩ := hd
  have ht : 0 < t := by omega
  by_contra hne
  apply hnp
  refine ⟨t + 1, by omega, 3, by omega, ?_⟩
  norm_num [polygonal]
  omega

/-- Marcus's conjecture: the three-four-five triple is the unique positive example. -/
theorem result : claim := by
  have small_nonpolygonal {n : Nat} (hn : n < 6) : nonpolygonal n := by
    rintro ⟨k, hk, m, hm, rfl⟩
    have hm3 : 3 ≤ m := by omega
    have hk1 : 1 ≤ k - 2 := by omega
    have hchoose : 3 ≤ Nat.choose m 2 := by
      simpa using Nat.choose_le_choose 2 hm3
    have hproduct : 3 ≤ (k - 2) * Nat.choose m 2 := by
      simpa using Nat.mul_le_mul hk1 hchoose
    simp only [polygonal] at hn
    omega
  have leg_dvd_three {x y z : Nat} (h : x ^ 2 + y ^ 2 = z ^ 2) :
      3 ∣ x ∨ 3 ∣ y := by
    have hmod : (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 = (z : ZMod 3) ^ 2 := by
      simpa using congrArg (fun n : Nat ↦ (n : ZMod 3)) h
    have hz : (x : ZMod 3) = 0 ∨ (y : ZMod 3) = 0 := by
      have residue : ∀ a b c : Fin 3,
          a ^ 2 + b ^ 2 = c ^ 2 → a = 0 ∨ b = 0 := by decide
      exact residue _ _ _ hmod
    rcases hz with hx | hy
    · exact Or.inl ((ZMod.natCast_eq_zero_iff x 3).mp hx)
    · exact Or.inr ((ZMod.natCast_eq_zero_iff y 3).mp hy)
  have solve_leg_three {y z : Nat} (hy : 0 < y)
      (h : 3 ^ 2 + y ^ 2 = z ^ 2) : y = 4 ∧ z = 5 := by
    have hyz : y < z := by nlinarith
    have hy4 : y ≤ 4 := by
      have hstep : (y + 1) ^ 2 ≤ z ^ 2 := by nlinarith
      nlinarith
    have hz5 : z ≤ 5 := by nlinarith
    interval_cases y <;> interval_cases z <;> norm_num at h
    norm_num
  constructor
  · exact ⟨small_nonpolygonal (by decide), small_nonpolygonal (by decide),
      small_nonpolygonal (by decide), by norm_num⟩
  intro x y z hx hy hxy hnx hny _hnz
  rcases leg_dvd_three hxy with h3x | h3y
  · have hx3 : x = 3 := eq_three_of_nonpolygonal_of_three_dvd hx hnx h3x
    subst x
    have hyz : y = 4 ∧ z = 5 := solve_leg_three hy hxy
    rcases hyz with ⟨rfl, rfl⟩
    norm_num
  · have hy3 : y = 3 := eq_three_of_nonpolygonal_of_three_dvd hy hny h3y
    subst y
    have hxz : x = 4 ∧ z = 5 := by
      apply solve_leg_three hx
      nlinarith
    rcases hxz with ⟨rfl, rfl⟩
    constructor
    · ext n
      simp [or_comm]
    · rfl

#print axioms result

end D5.S3.Arith.Congruence.MarcusPythagoreanNonpolygonalTriple
