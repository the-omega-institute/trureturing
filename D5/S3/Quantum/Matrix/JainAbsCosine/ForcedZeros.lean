/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Low even powers have vanishing Fourier modes above their finite frequency support. -/

import D5.S3.Quantum.Matrix.JainAbsCosine.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! Finite frequency support of even cosine powers on an odd grid. -/

open scoped BigOperators
open Finset

namespace D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
open D5.S3.Quantum.Matrix.JainAbsCosine.Defs

private noncomputable def moment (m j s : ℕ) : ℝ :=
  1 + 2 * ∑ l ∈ Icc 1 m,
    Real.cos (2 * (j : ℝ) * l * angle m) * Real.cos ((l : ℝ) * angle m) ^ (2 * s)

private lemma range_split (m : ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ range (m + 1), f l = f 0 + ∑ l ∈ Icc 1 m, f l := by
  have he : range (m + 1) = insert 0 (Icc 1 m) := by
    ext l
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [he, sum_insert (by simp)]

private lemma moment_zero (m j : ℕ) (hj : 1 ≤ j) (hjm : j < 2 * m + 1) :
    moment m j 0 = 0 := by
  have hd : 0 < 2 * (m : ℝ) + 1 := by positivity
  have ha : 0 < (j : ℝ) * angle m := by
    unfold angle
    positivity
  have hb : (j : ℝ) * angle m < Real.pi := by
    unfold angle
    have hjm' : (j : ℝ) < 2 * (m : ℝ) + 1 := by exact_mod_cast hjm
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).2
    nlinarith [Real.pi_pos]
  have hs := Real.sin_mul_sum_cos (m + 1) (2 * (j : ℝ) * angle m) 0
  have hsum : (∑ l ∈ range (m + 1),
      Real.cos (2 * (j : ℝ) * angle m * l + 0)) =
      1 + ∑ l ∈ Icc 1 m, Real.cos (2 * (j : ℝ) * l * angle m) := by
    rw [range_split]
    simp only [Nat.cast_zero, mul_zero, add_zero, Real.cos_zero]
    congr 1
    apply sum_congr rfl
    intro l _
    congr 1
    ring
  rw [hsum] at hs
  have hang : (2 * (m : ℝ) + 1) * ((j : ℝ) * angle m) = (j : ℝ) * Real.pi := by
    unfold angle
    field_simp
    <;> ring
  have hsin := Real.sin_add ((m + 1 : ℕ) * ((j : ℝ) * angle m))
    ((m : ℝ) * ((j : ℝ) * angle m))
  have hsub := Real.sin_sub ((m + 1 : ℕ) * ((j : ℝ) * angle m))
    ((m : ℝ) * ((j : ℝ) * angle m))
  have hplus : ((m + 1 : ℕ) : ℝ) * ((j : ℝ) * angle m) +
      (m : ℝ) * ((j : ℝ) * angle m) = (j : ℝ) * Real.pi := by
    push_cast
    linear_combination hang
  have hminus : ((m + 1 : ℕ) : ℝ) * ((j : ℝ) * angle m) -
      (m : ℝ) * ((j : ℝ) * angle m) = (j : ℝ) * angle m := by push_cast; ring
  rw [hplus, Real.sin_nat_mul_pi] at hsin
  rw [hminus] at hsub
  have harg1 : 2 * (j : ℝ) * angle m / 2 = (j : ℝ) * angle m := by ring
  have harg2 : ((m + 1 : ℕ) : ℝ) * (2 * (j : ℝ) * angle m) / 2 =
      ((m + 1 : ℕ) : ℝ) * ((j : ℝ) * angle m) := by ring
  have harg3 : (((m + 1 : ℕ) : ℝ) - 1) * (2 * (j : ℝ) * angle m) / 2 + 0 =
      (m : ℝ) * ((j : ℝ) * angle m) := by push_cast; ring
  rw [harg1, harg2, harg3] at hs
  have hmul : Real.sin ((j : ℝ) * angle m) * moment m j 0 = 0 := by
    simp only [moment, mul_zero, pow_zero, mul_one]
    linear_combination 2 * hs - hsin - hsub
  exact (mul_eq_zero.mp hmul).resolve_left
    (Real.sin_pos_of_pos_of_lt_pi ha hb).ne'

private lemma moment_step (m j s : ℕ) (hj : 1 ≤ j) :
    4 * moment m j (s + 1) =
      moment m (j - 1) s + 2 * moment m j s + moment m (j + 1) s := by
  have ht (l : ℕ) :
      4 * (Real.cos (2 * (j : ℝ) * l * angle m) *
        Real.cos ((l : ℝ) * angle m) ^ (2 * (s + 1))) =
      Real.cos (2 * ((j - 1 : ℕ) : ℝ) * l * angle m) *
          Real.cos ((l : ℝ) * angle m) ^ (2 * s) +
        2 * (Real.cos (2 * (j : ℝ) * l * angle m) *
          Real.cos ((l : ℝ) * angle m) ^ (2 * s)) +
        Real.cos (2 * ((j + 1 : ℕ) : ℝ) * l * angle m) *
          Real.cos ((l : ℝ) * angle m) ^ (2 * s) := by
    rw [Nat.cast_sub hj, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    rw [show 2 * ((j : ℝ) - 1) * l * angle m =
      2 * (j : ℝ) * l * angle m - 2 * ((l : ℝ) * angle m) by ring]
    rw [show 2 * ((j : ℝ) + 1) * l * angle m =
      2 * (j : ℝ) * l * angle m + 2 * ((l : ℝ) * angle m) by ring]
    rw [Real.cos_sub, Real.cos_add, Real.cos_two_mul,
      show 2 * (s + 1) = 2 * s + 2 by omega, pow_add]
    ring
  have hsum := sum_congr (s₁ := Icc 1 m) (s₂ := Icc 1 m) rfl (fun l _ => ht l)
  simp only [sum_add_distrib, ← mul_sum] at hsum
  unfold moment
  linear_combination 2 * hsum

private lemma moment_vanish (s : ℕ) :
    ∀ m j : ℕ, s < j → j + s < 2 * m + 1 → moment m j s = 0 := by
  induction s with
  | zero =>
    intro m j hj hm
    exact moment_zero m j (by omega) (by omega)
  | succ s ih =>
    intro m j hj hm
    have h₁ := ih m (j - 1) (by omega) (by omega)
    have h₂ := ih m j (by omega) (by omega)
    have h₃ := ih m (j + 1) (by omega) (by omega)
    have he := moment_step m j s (by omega)
    rw [h₁, h₂, h₃] at he
    linarith

/-- The Fourier modes above the degree of a low even cosine power vanish. -/
theorem modeValue_even_eq_zero (m j s : ℕ) (hsj : s < j) (hjm : j ≤ m) :
    modeValue m j (2 * (s : ℝ)) = 0 := by
  have he := moment_vanish s m j hsj (by omega)
  rw [show 2 * (s : ℝ) = ((2 * s : ℕ) : ℝ) by push_cast; ring]
  simpa only [modeValue, moment, Real.rpow_natCast] using he

/-- Two modes above the finite frequency support have zero difference. -/
theorem modeValue_gap_even_eq_zero (m j d s : ℕ) (hsj : s < j) (hjdm : j + d ≤ m) :
    modeValue m j (2 * (s : ℝ)) - modeValue m (j + d) (2 * (s : ℝ)) = 0 := by
  rw [modeValue_even_eq_zero m j s hsj (by omega),
    modeValue_even_eq_zero m (j + d) s (by omega) hjdm, sub_self]

end D5.S3.Quantum.Matrix.JainAbsCosine.ForcedZeros
