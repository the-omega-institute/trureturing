/- GID: D5/S1/Recurrence/SubsetSums/ModSixResidueCounts
   generality: I
   mirror-B: D5/B/S1/Recurrence/SubsetSums/ModSixResidueCounts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The full mod-six residue table proves Corneth's second A068012 recurrence. -/

import D5.S1.Recurrence.Parity.SubsetSumModSixDoubling

namespace D5.S1.Recurrence.SubsetSums.ModSixResidueCounts

open D5.S1.Recurrence.Parity.SubsetSumModSixDoubling

/-- The complete residue table for every `m ≥ 3`, with natural-number division. -/
theorem count_closed_form (m : ℕ) (hm : 3 ≤ m) (r : ZMod 6) :
    if m % 3 = 1 then
      if r = 2 ∨ r = 5 then 6 * C m r + 2 * 2 ^ (m / 3) = 2 ^ m
      else 6 * C m r = 2 ^ m + 2 ^ (m / 3)
    else
      if r = 0 ∨ r = 3 then 6 * C m r = 2 ^ m + 2 * 2 ^ (m / 3)
      else 6 * C m r + 2 ^ (m / 3) = 2 ^ m := by
  induction m, hm using Nat.le_induction generalizing r with
  | base => fin_cases r <;> decide
  | succ m hm ih =>
    have hfirst := ih r
    have hsecond := ih (r - (m + 1 : ℕ))
    have hquot : 2 ^ ((m + 1) / 3) =
        if m % 3 = 2 then 2 * 2 ^ (m / 3) else 2 ^ (m / 3) := by
      split_ifs with hrem
      · rw [show (m + 1) / 3 = m / 3 + 1 by omega, pow_succ, Nat.mul_comm]
      · rw [show (m + 1) / 3 = m / 3 by omega]
    have hcast : ((m + 1 : ℕ) : ZMod 6) = ((m % 6 : ℕ) : ZMod 6) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      congr 1
      exact (ZMod.natCast_eq_natCast_iff' m (m % 6) 6).mpr (by omega)
    have hmod : m % 3 = (m % 6) % 3 := by omega
    have hnext : (m + 1) % 3 = (m % 6 + 1) % 3 := by omega
    rw [count_succ, pow_succ, hquot, hcast]
    rw [hcast] at hsecond
    simp only [hmod] at hfirst hsecond ⊢
    rw [hnext]
    have hbound := Nat.mod_lt m (by decide : 0 < 6)
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
      exact (by decide : ∀ t : ZMod 6,
        t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5) r
    interval_cases hrem : m % 6 <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hfirst hsecond ⊢ <;>
      (try simp (disch := decide) only [if_pos, if_neg] at hfirst hsecond ⊢) <;> omega

/-- Corneth's second recurrence, with the correction moved left to avoid subtraction. -/
theorem corneth_step (k : ℕ) (hk : 1 ≤ k) :
    a (3 * k + 1) + 2 ^ (k - 1) = 2 * a (3 * k) := by
  have hzero := count_closed_form (3 * k) (by omega) 0
  have hone := count_closed_form (3 * k + 1) (by omega) 0
  have hdiv : (3 * k + 1) / 3 = k := by omega
  have hdivzero : 3 * k / 3 = k := by omega
  have hmod : (3 * k + 1) % 3 = 1 := by omega
  norm_num [hdivzero, hdiv, hmod, pow_succ] at hzero hone
  simp only [if_neg (by decide : ¬ ((0 : ZMod 6) = 2 ∨ (0 : ZMod 6) = 5))] at hone
  have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = k - 1 + 1 by omega]
    exact pow_succ _ _
  unfold a
  omega

#print axioms count_closed_form
#print axioms corneth_step

end D5.S1.Recurrence.SubsetSums.ModSixResidueCounts
