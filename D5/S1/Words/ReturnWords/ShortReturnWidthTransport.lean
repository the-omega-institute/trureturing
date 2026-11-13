/- GID: D5/S1/Words/ReturnWords/ShortReturnWidthTransport
   generality: G
   mirror-B: D5/B/S1/Words/ReturnWords/ShortReturnWidthTransport
   mirror-E: none(waiver:abstract-return-width-estimate)
   anchors: []
   utility: none
   digest: Finite interval chains supply packing bounds for short-return width transport. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-! Finite start-chain packing and phase-bounded conditional width transport. -/

namespace D5.S1.Words.ReturnWords.ShortReturnWidthTransport

/-- Adjacent separation accumulates along a finite chain of interval starts.
The final interval has length `ℓ`; only the first and last endpoints are constrained
by the parent. The conclusion is derived from local inequalities by induction. -/
theorem finite_interval_chain_packing {k : ℕ} (x : ℕ → ℝ) {δ ℓ u w : ℝ}
    (hleft : u ≤ x 0)
    (hstep : ∀ i < k, x i + δ ≤ x (i + 1))
    (hright : x k + ℓ ≤ u + w) :
    (k : ℝ) * δ + ℓ ≤ w := by
  have accumulated : ∀ m ≤ k, x 0 + (m : ℝ) * δ ≤ x m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        have hprev := ih (Nat.le_trans (Nat.le_succ m) hm)
        have hnext := hstep m (Nat.lt_of_succ_le hm)
        rw [Nat.cast_succ]
        linarith
  have htotal := accumulated k le_rfl
  linarith

/-- Affine images of a finite separated interval chain lie inside a parent interval.
The inclusion concerns the width-`w` images. The separate length-`d` intervals
`[x i, x i + d]` are ordered with disjoint interiors, allowing touching endpoints.
No claim identifies these abstract intervals with legal graph cylinders. -/
theorem affine_cylinder_chain_packing {k L : ℕ} {g d w u : ℝ} (x : ℕ → ℝ)
    (hg : 0 < g) (hw : 0 ≤ w)
    (hinside : ∀ i ≤ k,
      Set.Icc (u + g ^ L * x i) (u + g ^ L * (x i + w)) ⊆ Set.Icc u (u + w))
    (hseparated : ∀ i < k, x i + d ≤ x (i + 1)) :
    (k : ℝ) * (g ^ L * d) ≤ (1 - g ^ L) * w := by
  have hq : 0 ≤ g ^ L := (pow_pos hg L).le
  have hlen : 0 ≤ g ^ L * w := mul_nonneg hq hw
  have hend (i : ℕ) : u + g ^ L * x i ≤ u + g ^ L * (x i + w) := by
    nlinarith
  have hleft := (hinside 0 (Nat.zero_le k) ⟨le_rfl, hend 0⟩).1
  have hright := (hinside k le_rfl ⟨hend k, le_rfl⟩).2
  have hstep : ∀ i < k,
      (u + g ^ L * x i) + g ^ L * d ≤ u + g ^ L * x (i + 1) := by
    intro i hi
    have hscaled := mul_le_mul_of_nonneg_left (hseparated i hi) hq
    nlinarith
  have htotal := finite_interval_chain_packing
    (fun i => u + g ^ L * x i) (δ := g ^ L * d) (ℓ := g ^ L * w)
    (u := u) (w := w) hleft hstep (by nlinarith [hright])
  nlinarith

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

/-- Conditional width bridge from an explicit chain of affine intervals at the actual
least common multiple. Return existence, phase divisibility and the identification
with original legal cylinders remain hypotheses or outside the statement. -/
theorem short_return_width_lower_bound {a b n p k : ℕ} {g d w u : ℝ} (x : ℕ → ℝ)
    (hg : 0 < g) (hgone : g < 1) (hd : 0 ≤ d) (hw : 0 ≤ w) (hp : 0 < p)
    (ha0 : 0 < a) (hb0 : 0 < b) (hpa : p ∣ a) (hpb : p ∣ b)
    (ha : a ≤ n) (hb : b ≤ 2 * n - 1)
    (hinside : ∀ i ≤ k,
      Set.Icc (u + g ^ Nat.lcm a b * x i) (u + g ^ Nat.lcm a b * (x i + w)) ⊆
        Set.Icc u (u + w))
    (hseparated : ∀ i < k, x i + d ≤ x (i + 1)) :
    g ^ (p * (n / p) * ((2 * n - 1) / p)) /
      (1 - g ^ (p * (n / p) * ((2 * n - 1) / p))) * ((k : ℝ) * d) ≤ w := by
  have hpacking := affine_cylinder_chain_packing x hg hw hinside hseparated
  have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
  have hLM := synchronized_length_le_phase_bound hp hpa hpb ha hb
  have hratio := contraction_ratio_antitone hg hgone hL hLM
  have hden : 0 < 1 - g ^ Nat.lcm a b :=
    sub_pos.mpr (pow_lt_one₀ hg.le hgone (Nat.ne_of_gt hL))
  calc
    _ ≤ (g ^ Nat.lcm a b / (1 - g ^ Nat.lcm a b)) * ((k : ℝ) * d) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg (Nat.cast_nonneg k) hd)
    _ = (g ^ Nat.lcm a b * ((k : ℝ) * d)) / (1 - g ^ Nat.lcm a b) := by ring
    _ ≤ w := (div_le_iff₀ hden).2 (by nlinarith [hpacking])

end D5.S1.Words.ReturnWords.ShortReturnWidthTransport
