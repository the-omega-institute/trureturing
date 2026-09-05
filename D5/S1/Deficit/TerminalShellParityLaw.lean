/- GID: D5/S1/Deficit/TerminalShellParityLaw
   generality: G
   mirror-B: D5/B/S1/Deficit/TerminalShellParityLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The terminal sign law makes defect status equivalent to odd shell parity. -/

/- Library-search audit trail (2026-09-04):
   * D5 keyword, symbolic-shape, statement-body, digestion-index, and in-flight branch searches
     found no theorem identifying the terminal defect sign with shell parity.
   * Pinned Mathlib supplies `neg_one_pow_eq_one_iff_even`,
     `neg_one_pow_eq_neg_one_iff_odd`, and the natural-number successor parity laws. These are
     imported and used rather than reproved.
   * The source exponent contains `K - 1`; the explicit hypothesis `0 < K` rules out the
     totalized natural-subtraction branch at `K = 0`, where the claimed equivalence is false.
   * The retired `Meta/Digestion/formalizations/` receipt tree was neither inspected nor created.

   STOPPING JUSTIFICATION: this module proves clause (iv), the terminal parity law, under the
   stated first-sign regime. It does not formalize the empirical root schedule, finite-window
   scans, asymptotic error estimate, or the open middle-region boundary. -/

import Mathlib.Algebra.Ring.Int.Parity

namespace D5.S1.Deficit.TerminalShellParityLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem sign_pattern_eq_iff_odd (K a : ℕ) (hK : 0 < K) :
    (-1 : ℤ) ^ (K - 1 + a) = (-1 : ℤ) ^ a ↔ Odd K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  rw [Nat.succ_sub_one]
  obtain hk | hk := Nat.even_or_odd k
  · constructor
    · intro _
      exact hk.add_one
    · intro _
      have hkSign : (-1 : ℤ) ^ k = 1 := Even.neg_one_pow (α := ℤ) hk
      rw [pow_add, hkSign, one_mul]
  · constructor
    · intro hsign
      exfalso
      have hkSign : (-1 : ℤ) ^ k = -1 := Odd.neg_one_pow (α := ℤ) hk
      obtain ha | ha := Nat.even_or_odd a
      · have haSign : (-1 : ℤ) ^ a = 1 := Even.neg_one_pow (α := ℤ) ha
        simp [pow_add, hkSign, haSign] at hsign
      · have haSign : (-1 : ℤ) ^ a = -1 := Odd.neg_one_pow (α := ℤ) ha
        simp [pow_add, hkSign, haSign] at hsign
    · intro hkSucc
      exact ((Nat.not_odd_iff_even.mpr hk.add_one) hkSucc).elim

private theorem sign_pattern_opposite_iff_even (K a : ℕ) (hK : 0 < K) :
    (-1 : ℤ) ^ (K - 1 + a) = -(-1 : ℤ) ^ a ↔ Even K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  rw [Nat.succ_sub_one]
  obtain hk | hk := Nat.even_or_odd k
  · constructor
    · intro hsign
      exfalso
      have hkSign : (-1 : ℤ) ^ k = 1 := Even.neg_one_pow (α := ℤ) hk
      obtain ha | ha := Nat.even_or_odd a
      · have haSign : (-1 : ℤ) ^ a = 1 := Even.neg_one_pow (α := ℤ) ha
        simp [pow_add, hkSign, haSign] at hsign
      · have haSign : (-1 : ℤ) ^ a = -1 := Odd.neg_one_pow (α := ℤ) ha
        simp [pow_add, hkSign, haSign] at hsign
    · intro hkSucc
      exact ((Nat.not_even_iff_odd.mpr hk.add_one) hkSucc).elim
  · constructor
    · intro _
      exact hk.add_one
    · intro _
      have hkSign : (-1 : ℤ) ^ k = -1 := Odd.neg_one_pow (α := ℤ) hk
      rw [pow_add, hkSign, neg_one_mul]

/-- In the terminal regime, the first-term sign agrees with the defect sign exactly on odd
shells. Positivity of `K` is essential because natural subtraction is truncated at zero. -/
theorem terminal_shell_defect_iff_odd (K a : ℕ) (terminalSign : ℤ) (hK : 0 < K)
    (hfirst : terminalSign = (-1 : ℤ) ^ (K - 1 + a)) :
    terminalSign = (-1 : ℤ) ^ a ↔ Odd K := by
  rw [hfirst]
  exact sign_pattern_eq_iff_odd K a hK

/-- The complementary terminal sign occurs exactly on even shells. -/
theorem terminal_shell_conforming_iff_even (K a : ℕ) (terminalSign : ℤ) (hK : 0 < K)
    (hfirst : terminalSign = (-1 : ℤ) ^ (K - 1 + a)) :
    terminalSign = -(-1 : ℤ) ^ a ↔ Even K := by
  rw [hfirst]
  exact sign_pattern_opposite_iff_even K a hK

#print axioms terminal_shell_defect_iff_odd

end D5.S1.Deficit.TerminalShellParityLaw
