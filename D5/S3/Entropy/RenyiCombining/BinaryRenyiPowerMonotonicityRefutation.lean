/- GID: D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.claim; result=D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.result; claim=D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.claim
   digest: Powered binary Renyi entropy decreases between two positive orders at x = 1/17. -/

import D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining

/-!
The binary probability 1/17 separates the powered entropies at orders 1/4 and 1/2.
Exact integer power comparisons give rational bounds for the normalized entropies.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Entropy.RenyiCombining.BinaryRenyiPowerMonotonicityRefutation

open BinaryRenyiCombining

/-- Binary Renyi entropy normalized by the fair-bit entropy and raised to `2 / alpha`. -/
def powered (alpha x : ℝ) : ℝ := (hRenyi alpha x / Real.log 2) ^ (2 / alpha)

/-- Monotonicity in positive orders distinct from one, at every binary probability. -/
def claim : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ,
    0 < a → a < b → a ≠ 1 → b ≠ 1 → powered a x ≤ powered b x

private lemma entropy_quarter :
    hRenyi (1 / 4) (1 / 17) = (4 / 3) * (Real.log 3 - Real.log 17 / 4) := by
  have hr : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (4 : ℕ) ≠ 0) using 1
    norm_num
  unfold hRenyi
  rw [show (1 - 1 / 17 : ℝ) = 16 / 17 by norm_num,
    Real.div_rpow (by norm_num) (by norm_num),
    Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, hr,
    show 1 / (17 : ℝ) ^ (1 / 4 : ℝ) + 2 / (17 : ℝ) ^ (1 / 4 : ℝ) =
      3 / (17 : ℝ) ^ (1 / 4 : ℝ) by ring,
    Real.log_div (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 17) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 17)]
  ring

private lemma entropy_half : hRenyi (1 / 2) (1 / 17) = Real.log (25 / 17) := by
  have hr : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4)
      (by norm_num : (2 : ℕ) ≠ 0) using 1
    norm_num
  have hl : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    convert Real.log_pow (5 : ℝ) 2 using 1
    norm_num
  unfold hRenyi
  rw [show (1 - 1 / 17 : ℝ) = 16 / 17 by norm_num,
    Real.div_rpow (by norm_num) (by norm_num),
    Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, hr,
    show 1 / (17 : ℝ) ^ (1 / 2 : ℝ) + 4 / (17 : ℝ) ^ (1 / 2 : ℝ) =
      5 / (17 : ℝ) ^ (1 / 2 : ℝ) by ring,
    Real.log_div (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 17) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 17),
    Real.log_div (by norm_num) (by norm_num), hl]
  ring

private lemma quarter_lower :
    (3 / 4 : ℝ) < hRenyi (1 / 4) (1 / 17) / Real.log 2 := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  rw [entropy_quarter]
  have h : Real.log ((17 : ℝ) ^ 4 * 2 ^ 9) < Real.log ((3 : ℝ) ^ 16) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private lemma half_bounds :
    0 < hRenyi (1 / 2) (1 / 17) / Real.log 2 ∧
      hRenyi (1 / 2) (1 / 17) / Real.log 2 < (9 / 16 : ℝ) := by
  rw [entropy_half]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 25 / 17)) htwo
  · apply (div_lt_iff₀ htwo).2
    have h : Real.log ((25 / 17 : ℝ) ^ 16) < Real.log ((2 : ℝ) ^ 9) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith

private lemma powered_reverse : powered (1 / 2) (1 / 17) < powered (1 / 4) (1 / 17) := by
  have hhalf := pow_lt_pow_left₀ half_bounds.2 half_bounds.1.le
    (by norm_num : (4 : ℕ) ≠ 0)
  have hquarter := pow_lt_pow_left₀ quarter_lower (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (8 : ℕ) ≠ 0)
  unfold powered
  rw [show (2 / (1 / 2) : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    show (2 / (1 / 4) : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast _ 4, Real.rpow_natCast _ 8]
  exact hhalf.trans (lt_of_eq_of_lt (by norm_num) hquarter)

/-- The probability `1/17` violates monotonicity between orders `1/4` and `1/2`. -/
theorem result : ¬ claim := by
  intro h
  have hle := h (1 / 17) (by constructor <;> norm_num) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (not_le_of_gt powered_reverse) hle

end D5.S3.Entropy.RenyiCombining.BinaryRenyiPowerMonotonicityRefutation
