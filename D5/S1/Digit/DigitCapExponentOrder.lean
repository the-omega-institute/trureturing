/- GID: D5/S1/Digit/DigitCapExponentOrder
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapExponentOrder
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Bounded-digit growth exponents are real, nonnegative, ordered and monotone in the cap. -/

import D5.S1.Digit.DigitCapQuotientBound
import D5.S1.Digit.DigitCapLowerExponent

/-! # Real values, order and cap monotonicity of the bounded-digit growth exponents

For a radix `ell ≥ 2` and a digit cap `k ≥ ell - 1`, the logarithmic readout
`log (count k ell n) / log n` lies in `[0, log (k + 1) / log ell]` for every `n ≥ 2`.
Hence both the upper and the lower every-tail limits are finite nonnegative real numbers,
the lower one does not exceed the upper one, and both are monotone in the cap.
-/

namespace D5.S1.Digit.DigitCapExponentOrder

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapQuotientBound
open D5.S1.Digit.DigitCapLowerExponent

private lemma count_mono (k ell n : ℕ) (hell : 2 ≤ ell) :
    count k ell n ≤ count (k + 1) ell n := by
  have := partitions_finite (k + 1) ell n hell
  exact Nat.card_le_card_of_injective
    (fun a => ⟨a.val, fun i => le_trans (a.property.1 i) (Nat.le_succ k), a.property.2⟩)
    (by
      intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this)

private lemma readout_nonneg (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hn : 2 ≤ n) : 0 ≤ readout k ell n := by
  unfold readout
  have hc : (1 : ℝ) ≤ (count k ell n : ℝ) := by
    exact_mod_cast count_positive k ell n hell hk
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact div_nonneg (Real.log_nonneg hc) hl.le

private lemma readout_mono (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hn : 2 ≤ n) : readout k ell n ≤ readout (k + 1) ell n := by
  unfold readout
  have hc : (0 : ℝ) < (count k ell n : ℝ) := by
    exact_mod_cast count_positive k ell n hell hk
  have hm : (count k ell n : ℝ) ≤ (count (k + 1) ell n : ℝ) := by
    exact_mod_cast count_mono k ell n hell
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact div_le_div_of_nonneg_right (Real.log_le_log hc hm) hl.le

private lemma readout_le (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hn : 2 ≤ n) : readout k ell n ≤ Real.log (k + 1) / Real.log ell := by
  set m := Nat.log ell n
  have hlt : n < ell ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hge : ell ^ m ≤ n := Nat.pow_log_le_self ell (by omega)
  have hcap : k ≤ (k + 1) * ell - 1 := by
    have : (k + 1) * 2 ≤ (k + 1) * ell := Nat.mul_le_mul_left _ hell
    omega
  have hcount : count k ell n ≤ (k + 1) ^ m :=
    count_le_pow ell (k + 1) m k n hell (by omega) hcap hlt
  have hc : (0 : ℝ) < (count k ell n : ℝ) := by
    exact_mod_cast count_positive k ell n hell hk
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by exact_mod_cast hell)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hk1 : 0 ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have h1 : Real.log (count k ell n : ℝ) ≤ m * Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_pow]
    apply Real.log_le_log hc
    exact_mod_cast hcount
  have h2 : (m : ℝ) * Real.log (ell : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hge
  unfold readout
  rw [div_le_div_iff₀ hlogn hlogell]
  calc Real.log (count k ell n : ℝ) * Real.log (ell : ℝ)
      ≤ (m * Real.log ((k : ℝ) + 1)) * Real.log (ell : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hlogell.le
    _ = ((m : ℝ) * Real.log (ell : ℝ)) * Real.log ((k : ℝ) + 1) := by ring
    _ ≤ Real.log (n : ℝ) * Real.log ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h2 hk1
    _ = Real.log ((k : ℝ) + 1) * Real.log (n : ℝ) := by ring

/-- For every radix `ell ≥ 2` and every digit cap `k ≥ ell - 1`, the upper and lower
logarithmic growth exponents are finite nonnegative real numbers, the lower one is at most
the upper one, and both do not decrease when the cap grows by one. -/
theorem exponents_real_ordered_monotone (ell k : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k) :
    (∃ A L : ℝ, exponent k ell = A ∧ lowerExponent k ell = L ∧ 0 ≤ L ∧ L ≤ A) ∧
      exponent k ell ≤ exponent (k + 1) ell ∧
      lowerExponent k ell ≤ lowerExponent (k + 1) ell := by
  set C : ℝ := Real.log (k + 1) / Real.log ell
  have hnn : ∀ n, 2 ≤ n → (0 : EReal) ≤ (readout k ell n : EReal) := fun n hn =>
    EReal.coe_nonneg.mpr (readout_nonneg k ell n hell hk hn)
  have hle : ∀ n, 2 ≤ n → (readout k ell n : EReal) ≤ (C : EReal) := fun n hn =>
    EReal.coe_le_coe_iff.mpr (readout_le k ell n hell hk hn)
  have hA0 : (0 : EReal) ≤ exponent k ell := by
    unfold exponent
    exact le_iInf₂ fun N hN => le_iSup₂_of_le N le_rfl (hnn N hN)
  have hAC : exponent k ell ≤ (C : EReal) := by
    unfold exponent
    exact iInf₂_le_of_le 2 le_rfl (iSup₂_le fun n hn => hle n (by omega))
  have hL0 : (0 : EReal) ≤ lowerExponent k ell := by
    unfold lowerExponent
    exact le_iSup₂_of_le 2 le_rfl (le_iInf₂ fun n hn => hnn n (by omega))
  have hLC : lowerExponent k ell ≤ (C : EReal) := by
    unfold lowerExponent
    exact iSup₂_le fun N hN => iInf₂_le_of_le N le_rfl (hle N hN)
  have hLA : lowerExponent k ell ≤ exponent k ell := by
    unfold lowerExponent exponent
    refine iSup₂_le fun N _ => le_iInf₂ fun M _ => ?_
    exact (iInf₂_le (max N M) (le_max_left N M)).trans
      (le_iSup₂ (f := fun n (_ : M ≤ n) => (readout k ell n : EReal)) (max N M)
        (le_max_right N M))
  have hfin : ∀ x : EReal, 0 ≤ x → x ≤ (C : EReal) → (x.toReal : EReal) = x := by
    intro x h0 hC
    apply EReal.coe_toReal
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top C) hC
    · exact ne_bot_of_le_ne_bot EReal.zero_ne_bot h0
  refine ⟨⟨(exponent k ell).toReal, (lowerExponent k ell).toReal,
    (hfin _ hA0 hAC).symm, (hfin _ hL0 hLC).symm, ?_, ?_⟩, ?_, ?_⟩
  · rw [← EReal.coe_nonneg, hfin _ hL0 hLC]
    exact hL0
  · rw [← EReal.coe_le_coe_iff, hfin _ hL0 hLC, hfin _ hA0 hAC]
    exact hLA
  · unfold exponent
    exact iInf₂_mono fun N hN => iSup₂_mono fun n hn =>
      EReal.coe_le_coe_iff.mpr (readout_mono k ell n hell hk (by omega))
  · unfold lowerExponent
    exact iSup₂_mono fun N hN => iInf₂_mono fun n hn =>
      EReal.coe_le_coe_iff.mpr (readout_mono k ell n hell hk (by omega))

end D5.S1.Digit.DigitCapExponentOrder
