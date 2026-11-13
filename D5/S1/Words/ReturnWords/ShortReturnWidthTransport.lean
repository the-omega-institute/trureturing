/- GID: D5/S1/Words/ReturnWords/ShortReturnWidthTransport
   generality: G
   mirror-B: D5/B/S1/Words/ReturnWords/ShortReturnWidthTransport
   mirror-E: none(waiver:abstract-return-width-estimate)
   anchors: []
   utility: none
   digest: Phase divisibility bounds synchronized return lengths and transports contraction widths. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace D5.S1.Words.ReturnWords.ShortReturnWidthTransport

/-- Arithmetic synchronization bound for two lengths divisible by a common phase period.
No existence of graph returns is asserted. Natural division is floor division. -/
theorem synchronized_length_le_phase_bound {a b n p : ℕ} (hp : 0 < p)
    (hpa : p ∣ a) (hpb : p ∣ b) (ha : a ≤ n) (hb : b ≤ 2 * n - 1) :
    Nat.lcm a b ≤ p * (n / p) * ((2 * n - 1) / p) := by
  obtain ⟨α, rfl⟩ := hpa
  obtain ⟨γ, rfl⟩ := hpb
  have hα : α ≤ n / p := (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using ha)
  have hγ : γ ≤ (2 * n - 1) / p :=
    (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hb)
  have hlcm : Nat.lcm α γ ≤ α * γ := by
    by_cases hαzero : α = 0
    · simp [hαzero]
    by_cases hγzero : γ = 0
    · simp [hγzero]
    exact Nat.lcm_le_mul (Nat.pos_of_ne_zero hαzero) (Nat.pos_of_ne_zero hγzero)
  rw [Nat.lcm_mul_left]
  calc
    p * Nat.lcm α γ ≤ p * (α * γ) := Nat.mul_le_mul_left p hlcm
    _ ≤ p * ((n / p) * ((2 * n - 1) / p)) :=
      Nat.mul_le_mul_left p (Nat.mul_le_mul hα hγ)
    _ = p * (n / p) * ((2 * n - 1) / p) := (Nat.mul_assoc _ _ _).symm

/-- A longer positive synchronization scale gives a smaller contraction lower bound.
Both denominators are positive, including when the two scales are equal. -/
theorem contraction_ratio_antitone {g : ℝ} (hg : 0 < g) (hgone : g < 1)
    {L M : ℕ} (hL : 0 < L) (hLM : L ≤ M) :
    g ^ M / (1 - g ^ M) ≤ g ^ L / (1 - g ^ L) := by
  have hpow : g ^ M ≤ g ^ L := pow_le_pow_of_le_one hg.le hgone.le hLM
  have hden : 0 < 1 - g ^ L := sub_pos.mpr (pow_lt_one₀ hg.le hgone (Nat.ne_of_gt hL))
  exact div_le_div₀ (pow_nonneg hg.le L) hpow hden (sub_le_sub_left hpow 1)

/-- Conditional width bridge for short returns. The graph/source argument must supply
positive lengths, phase divisibility, the short-return bounds and the packing estimate
at their actual least common multiple. This theorem supplies none of those premises. -/
theorem short_return_width_lower_bound {a b n p : ℕ} {g d w : ℝ}
    (hg : 0 < g) (hgone : g < 1) (hd : 0 ≤ d) (hp : 0 < p)
    (ha0 : 0 < a) (hb0 : 0 < b) (hpa : p ∣ a) (hpb : p ∣ b)
    (ha : a ≤ n) (hb : b ≤ 2 * n - 1)
    (hpacking : g ^ Nat.lcm a b * d ≤ (1 - g ^ Nat.lcm a b) * w) :
    g ^ (p * (n / p) * ((2 * n - 1) / p)) /
      (1 - g ^ (p * (n / p) * ((2 * n - 1) / p))) * d ≤ w := by
  have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
  have hLM := synchronized_length_le_phase_bound hp hpa hpb ha hb
  have hratio := contraction_ratio_antitone hg hgone hL hLM
  have hden : 0 < 1 - g ^ Nat.lcm a b :=
    sub_pos.mpr (pow_lt_one₀ hg.le hgone (Nat.ne_of_gt hL))
  calc
    _ ≤ (g ^ Nat.lcm a b / (1 - g ^ Nat.lcm a b)) * d :=
      mul_le_mul_of_nonneg_right hratio hd
    _ = (g ^ Nat.lcm a b * d) / (1 - g ^ Nat.lcm a b) := by ring
    _ ≤ w := (div_le_iff₀ hden).2 (by simpa [mul_comm] using hpacking)

end D5.S1.Words.ReturnWords.ShortReturnWidthTransport
