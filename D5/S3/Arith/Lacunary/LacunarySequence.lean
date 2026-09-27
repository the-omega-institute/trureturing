/- GID: D5/S3/Arith/Lacunary/LacunarySequence
   generality: G
   mirror-B: D5/B/S3/Arith/Lacunary/LacunarySequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Base]
   utility: none
   digest: A lacunary sequence grows at least geometrically, so few of its terms lie below a bound. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
namespace D5.S3.Arith.Lacunary.LacunarySequence

/-- A positive real sequence is lacunary with ratio `c` if `1 < c` and each term
is at least `c` times its predecessor. -/
def IsLacunary (a : ℕ → ℝ) (c : ℝ) : Prop :=
  1 < c ∧ (∀ n, 0 < a n) ∧ ∀ n, c * a n ≤ a (n + 1)

/-- A lacunary sequence dominates the geometric sequence with the same initial term. -/
theorem geometric_lower_bound {a : ℕ → ℝ} {c : ℝ} (h : IsLacunary a c) (n : ℕ) :
    a 0 * c ^ n ≤ a n := by
  have hc : 0 < c := lt_trans zero_lt_one h.1
  induction n with
  | zero => simp only [pow_zero, mul_one, le_refl]
  | succ n ih =>
    calc
      a 0 * c ^ (n + 1) = (a 0 * c ^ n) * c := by rw [pow_succ, mul_assoc]
      _ ≤ a n * c := mul_le_mul_of_nonneg_right ih hc.le
      _ = c * a n := mul_comm _ _
      _ ≤ a (n + 1) := h.2.2 n

/-- The length of an initial segment bounded by `x` is at most the nonnegative
part of the logarithmic bound. The maximum handles the empty segment, for which
`x` is unrestricted and the untruncated logarithmic bound can be negative. -/
theorem card_lt_of_lacunary {a : ℕ → ℝ} {c : ℝ} (h : IsLacunary a c) (x : ℝ) (N : ℕ)
    (hmem : ∀ n < N, a n ≤ x) : (N : ℝ) ≤ max 0 (Real.logb c (x / a 0) + 1) := by
  have hc : 0 < c := lt_trans zero_lt_one h.1
  have ha : 0 < a 0 := h.2.1 0
  cases N with
  | zero =>
    rw [Nat.cast_zero]
    exact le_max_left (0 : ℝ) (Real.logb c (x / a 0) + 1)
  | succ n =>
    have hg : a 0 * c ^ n ≤ x :=
      (geometric_lower_bound h n).trans (hmem n (Nat.lt_succ_self n))
    have hp : c ^ n ≤ x / a 0 :=
      (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hg)
    have hl : Real.logb c (c ^ n) ≤ Real.logb c (x / a 0) :=
      Real.logb_le_logb_of_le h.1 (pow_pos hc n) hp
    rw [Real.logb_pow, Real.logb_self_eq_one h.1, mul_one] at hl
    calc
      ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_add_one n
      _ ≤ Real.logb c (x / a 0) + 1 := add_le_add hl (le_refl 1)
      _ ≤ max 0 (Real.logb c (x / a 0) + 1) := le_max_right _ _

end D5.S3.Arith.Lacunary.LacunarySequence
