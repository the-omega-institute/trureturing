/- GID: D5/S1/Recurrence/WilsonPisotL67Recurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/WilsonPisotL67Recurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The native Pisot sequence L(6,7) satisfies Wilson's signed recurrence. -/

import Mathlib.Tactic

/-! The elementary second-difference and determinant induction is the prior public
proof outline in the-omega-institute/trureturing#21793. The native definition and
four-lag claim are OEIS A048585, revision 18. -/

namespace D5.S1.Recurrence.WilsonPisotL67Recurrence

/-- The native integer-valued sequence, with ordinary rational upward ceiling. -/
noncomputable def a : ℕ → ℤ
  | 0 => 6
  | 1 => 7
  | n + 2 => ⌈(a (n + 1) : ℚ) ^ 2 / (a n : ℚ)⌉

private def v : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => 6
  | n + 3 => v (n + 2) + v n

private def s (n : ℕ) : ℤ := v (n + 2) - 2 * v (n + 1) + v n
private def d (n : ℕ) : ℤ := v n * v (n + 2) - v (n + 1) ^ 2
private def u (n : ℕ) : ℤ := v n + 3

private theorem v_rec (n : ℕ) : v (n + 3) = v (n + 2) + v n := by rfl

private theorem s_rec (n : ℕ) : s (n + 3) = s (n + 2) + s n := by
  simp only [s, v_rec]
  ring

private theorem d_rec (n : ℕ) : d (n + 3) = d n - d (n + 1) := by
  simp only [d, v_rec]
  ring

private theorem v_pos (n : ℕ) : 0 < v n := by
  induction n using Nat.stepInduction 3 with
  | base n hn => interval_cases n <;> norm_num [v]
  | step n ih =>
    rw [v_rec]
    have h0 := ih 0 (by omega)
    have h2 := ih 2 (by omega)
    simp only [Nat.add_zero] at h0
    omega

private theorem s_pos (n : ℕ) : 0 < s n := by
  induction n using Nat.stepInduction 3 with
  | base n hn => interval_cases n <;> norm_num [s, v]
  | step n ih =>
    rw [s_rec]
    have h0 := ih 0 (by omega)
    have h2 := ih 2 (by omega)
    simp only [Nat.add_zero] at h0
    omega

private theorem s_mono (n : ℕ) : s n ≤ s (n + 1) := by
  induction n using Nat.stepInduction 3 with
  | base n hn => interval_cases n <;> norm_num [s, v]
  | step n ih =>
    have h0 := ih 0 (by omega)
    have h2 := ih 2 (by omega)
    simp only [Nat.add_zero] at h0
    rw [s_rec n, show n + 3 + 1 = (n + 1) + 3 by omega, s_rec]
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    omega

private theorem determinant_bounds (n : ℕ) :
    -s (n + 7) ≤ d (n + 7) ∧ d (n + 7) ≤ s (n + 7) := by
  induction n using Nat.stepInduction 3 with
  | base n hn => interval_cases n <;> norm_num [s, d, v]
  | step n ih =>
    have h0 := ih 0 (by omega)
    have h1 := ih 1 (by omega)
    have hm := s_mono (n + 8)
    simp only [Nat.add_zero] at h0
    rw [show n + 3 + 7 = (n + 7) + 3 by omega, d_rec, s_rec]
    have e1 : n + 1 + 7 = n + 7 + 1 := by omega
    have e2 : n + 8 = n + 7 + 1 := by omega
    have e3 : n + 8 + 1 = n + 7 + 2 := by omega
    rw [e1] at h1
    rw [e2, e3] at hm
    constructor <;> omega

private theorem scale_bound (n : ℕ) : 4 * s (n + 7) < v (n + 7) := by
  induction n using Nat.stepInduction 3 with
  | base n hn => interval_cases n <;> norm_num [s, v]
  | step n ih =>
    have h0 := ih 0 (by omega)
    have h2 := ih 2 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show n + 3 + 7 = (n + 7) + 3 by omega, s_rec, v_rec]
    have e2 : n + 2 + 7 = n + 7 + 2 := by omega
    rw [e2] at h2
    omega

private theorem error_eq (n : ℕ) :
    u n * u (n + 2) - u (n + 1) ^ 2 = d n + 3 * s n := by
  simp only [u, d, s]
  ring

private theorem window (n : ℕ) : 0 < u n ∧
    0 ≤ u n * u (n + 2) - u (n + 1) ^ 2 ∧
    u n * u (n + 2) - u (n + 1) ^ 2 < u n := by
  have hp := v_pos n
  constructor
  · dsimp [u]; omega
  · by_cases hn : n < 7
    · interval_cases n <;> norm_num [u, v]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      rw [error_eq]
      have hd := determinant_bounds k
      have hs := s_pos (k + 7)
      have hv := scale_bound k
      dsimp [u]
      constructor <;> omega

private theorem u_ceiling (n : ℕ) :
    ⌈(u (n + 1) : ℚ) ^ 2 / (u n : ℚ)⌉ = u (n + 2) := by
  obtain ⟨hp, hlo, hhi⟩ := window n
  have hpq : (0 : ℚ) < u n := by exact_mod_cast hp
  have hloq : (0 : ℚ) ≤ (u n : ℚ) * u (n + 2) - (u (n + 1) : ℚ) ^ 2 := by
    exact_mod_cast hlo
  have hhiq : (u n : ℚ) * u (n + 2) - (u (n + 1) : ℚ) ^ 2 < u n := by
    exact_mod_cast hhi
  apply Int.ceil_eq_iff.mpr
  constructor
  · apply (lt_div_iff₀ hpq).mpr
    nlinarith
  · apply (div_le_iff₀ hpq).mpr
    nlinarith

private theorem native_eq (n : ℕ) : a n = u n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [a, u, v]
  | one => norm_num [a, u, v]
  | more n h0 h1 => rw [a, h0, h1, u_ceiling]

/-- Positivity and Wilson's signed recurrence, at every natural index in range. -/
theorem result : (∀ n : ℕ, 0 < a n) ∧
    ∀ n : ℕ, 4 ≤ n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 3) - a (n - 4) := by
  constructor
  · intro n
    rw [native_eq]
    exact (window n).1
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega,
      show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega,
      show k + 4 - 4 = k by omega, native_eq, u]
    rw [show k + 4 = (k + 1) + 3 by omega, v_rec, v_rec]
    ring

end D5.S1.Recurrence.WilsonPisotL67Recurrence
