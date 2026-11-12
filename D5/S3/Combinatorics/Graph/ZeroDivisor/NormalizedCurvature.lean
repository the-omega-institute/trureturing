/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/NormalizedCurvature
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/NormalizedCurvature
   mirror-E: none(waiver:uniform-normalized-binomial-curvature)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Cast]
   utility: none
   digest: Normalized binomial second differences satisfy a uniform curvature bound. -/

import D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction
import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature

open Finset

/-- The normalized second difference is the marked-prefix and unmarked-pair ratio. -/
theorem normalized_second_difference (N m k : ℕ) (hm : m ≤ N)
    (hk : 1 ≤ k) (hkN : k < N) :
    (m.choose (k-1) : ℚ) / (N.choose (k-1) : ℚ) -
        2 * ((m.choose k : ℚ) / (N.choose k : ℚ)) +
        (m.choose (k+1) : ℚ) / (N.choose (k+1) : ℚ) =
      (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) /
        ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
  have step (n j : ℕ) : (n.choose (j+1) : ℚ) * (j+1) =
      (n.choose j : ℚ) * ((n : ℚ)-j) := by
    by_cases hj : j ≤ n
    · have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using h
    · have hj' : n < j := by omega
      simp [Nat.choose_eq_zero_of_lt hj',
        Nat.choose_eq_zero_of_lt (by omega : n < j+1)]
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have hkp0 : (k : ℚ)+1 ≠ 0 := by positivity
  have hA : (N.choose (k-1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k-1 ≤ N)
  have hNk : (N : ℚ)-(k : ℚ) ≠ 0 := by
    have : (k : ℚ) < N := by exact_mod_cast hkN
    linarith
  have hNk1 : (N : ℚ)-(k : ℚ)+1 ≠ 0 := by
    have : (k : ℚ) < N := by exact_mod_cast hkN
    linarith
  have vstep := step m (k-1)
  have bstep := step N (k-1)
  simp only [Nat.sub_add_cancel hk, Nat.cast_sub hk, Nat.cast_one] at vstep bstep
  have vform : (m.choose k : ℚ) =
      (m.choose (k-1) : ℚ) * ((m : ℚ)-k+1) / k := by
    apply (eq_div_iff hk0).mpr
    linear_combination vstep
  have bform : (N.choose k : ℚ) =
      (N.choose (k-1) : ℚ) * ((N : ℚ)-k+1) / k := by
    apply (eq_div_iff hk0).mpr
    linear_combination bstep
  have wform : (m.choose (k+1) : ℚ) =
      (m.choose (k-1) : ℚ) * ((m : ℚ)-k+1) * ((m : ℚ)-k) /
        ((k : ℚ)*((k : ℚ)+1)) := by
    have h := step m k
    rw [vform] at h
    field_simp [hk0, hkp0] at h ⊢
    nlinarith [h]
  have cform : (N.choose (k+1) : ℚ) =
      (N.choose (k-1) : ℚ) * ((N : ℚ)-k+1) * ((N : ℚ)-k) /
        ((k : ℚ)*((k : ℚ)+1)) := by
    have h := step N k
    rw [bform] at h
    field_simp [hk0, hkp0] at h ⊢
    nlinarith [h]
  rw [vform, wform, bform, cform, Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_sub hm]
  push_cast
  field_simp [hA, hk0, hkp0, hNk, hNk1]
  <;> ring

/-- A uniform curvature bound, including the three small ranks. -/
theorem normalized_second_difference_bound (N m k : ℕ) (hN : 9 ≤ N)
    (hm : m ≤ N) (hk : 3 ≤ k) (hkN : k < N) :
    (m.choose (k-1) : ℚ) / (N.choose (k-1) : ℚ) -
        2 * ((m.choose k : ℚ) / (N.choose k : ℚ)) +
        (m.choose (k+1) : ℚ) / (N.choose (k+1) : ℚ) ≤
      1 / (3 * ((k : ℚ)+1)) := by
  rw [normalized_second_difference N m k hm (by omega) hkN]
  by_cases hk6 : 6 ≤ k
  · have hmn : m+(N-m) = N := by omega
    have hvand := Nat.add_choose_eq m (N-m) (k+1)
    rw [hmn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hvand
    have hterm : m.choose (k-1) * (N-m).choose 2 ≤ N.choose (k+1) := by
      rw [hvand]
      have h := Finset.single_le_sum
        (f := fun j => m.choose j * (N-m).choose (k+1-j))
        (s := range (k+1+1)) (by intro j _; exact Nat.zero_le _)
        (show k-1 ∈ range (k+1+1) from mem_range.mpr (by omega))
      simpa only [show k+1-(k-1) = 2 by omega] using h
    have htermQ : (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) ≤
        (N.choose (k+1) : ℚ) := by exact_mod_cast hterm
    have hD : 0 < (N.choose (k+1) : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : k+1 ≤ N)
    have hP : 0 < ((k+1).choose 2 : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : 2 ≤ k+1)
    calc
      _ ≤ (N.choose (k+1) : ℚ) /
          ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) :=
        (div_le_div_iff_of_pos_right (mul_pos hD hP)).mpr htermQ
      _ = 1 / ((k+1).choose 2 : ℚ) := by
        field_simp
      _ ≤ 1 / (3 * ((k : ℚ)+1)) := by
        apply one_div_le_one_div_of_le (by positivity)
        rw [Nat.cast_choose_two]
        push_cast
        have hk6Q : (6 : ℚ) ≤ k := by exact_mod_cast hk6
        nlinarith
  · have hsmall := NineRestriction.nine_restriction_bound N m k hN hm
      (show 3 ≤ k ∧ k ≤ 5 by omega)
    rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with h | h | h <;>
      subst k <;> norm_num at hsmall ⊢ <;> linarith

end D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature
