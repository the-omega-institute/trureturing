/- GID: D5/S3/Arith/Congruence/TernaryRootLoadTail
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TernaryRootLoadTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite ternary-root itinerary obeys an explicit discounted load-square bound. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace D5.S3.Arith.Congruence.TernaryRootLoadTail

/-- Normalized remaining pure-ternary load-square cost, recording the
number of previous test depths assigned to each surviving ternary root. -/
noncomputable def rootLoadTail (d₀ d₁ : ℝ) (a b : ℕ) : List Bool → ℝ
  | [] => 0
  | false :: rest => (3 + 2 * (a : ℝ)) * d₀ + rootLoadTail d₀ d₁ (a + 1) b rest / 3
  | true :: rest => (3 + 2 * (b : ℝ)) * d₁ + rootLoadTail d₀ d₁ a (b + 1) rest / 3

/-- No finite interleaving of the two roots exceeds the larger of the
infinite constant-root costs. The bound is uniform in the number of depths. -/
theorem root_load_tail_le (d₀ d₁ : ℝ) (h₀ : 0 ≤ d₀) (h₁ : 0 ≤ d₁)
    (a b : ℕ) (itinerary : List Bool) :
    rootLoadTail d₀ d₁ a b itinerary ≤
      3 * max (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2)) := by
  induction itinerary generalizing a b with
  | nil =>
      simp only [rootLoadTail]
      positivity
  | cons c rest ih =>
      cases c with
      | false =>
          simp only [rootLoadTail]
          have h := ih (a + 1) b
          simp only [Nat.cast_add, Nat.cast_one] at h
          have hm₀ := le_max_left (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2))
          have hm₁ := le_max_right (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2))
          rcases le_total (d₀ * (((a : ℝ) + 1) + 2)) (d₁ * ((b : ℝ) + 2)) with hc | hc
          · rw [max_eq_right hc] at h
            nlinarith
          · rw [max_eq_left hc] at h
            nlinarith
      | true =>
          simp only [rootLoadTail]
          have h := ih a (b + 1)
          simp only [Nat.cast_add, Nat.cast_one] at h
          have hm₀ := le_max_left (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2))
          have hm₁ := le_max_right (d₀ * ((a : ℝ) + 2)) (d₁ * ((b : ℝ) + 2))
          rcases le_total (d₀ * ((a : ℝ) + 2)) (d₁ * (((b : ℝ) + 1) + 2)) with hc | hc
          · rw [max_eq_right hc] at h
            nlinarith
          · rw [max_eq_left hc] at h
            nlinarith

#print axioms root_load_tail_le
end D5.S3.Arith.Congruence.TernaryRootLoadTail
