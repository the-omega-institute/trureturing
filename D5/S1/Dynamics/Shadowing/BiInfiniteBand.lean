/- GID: D5/S1/Dynamics/Shadowing/BiInfiniteBand
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/BiInfiniteBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite consecutive transition bands in bi-infinite scalar sequences. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Local barriers and accumulated middle progress classify transition times. -/

namespace D5.S1.Dynamics.Shadowing

/-- Integer times at which a scalar sequence lies strictly between two barriers. -/
def bandMarkers (x : ℤ → ℝ) (a b : ℝ) : Set ℤ := {k | a < x k ∧ x k < b}

/-- Local barriers and a uniform advance inside the open transition band. -/
structure ScalarBandProgress (x : ℤ → ℝ) (a b η : ℝ) : Prop where
  lower_back : ∀ k, x (k + 1) ≤ a → x k ≤ a
  upper_forward : ∀ k, b ≤ x k → b ≤ x (k + 1)
  no_jump : ∀ k, x k ≤ a → x (k + 1) < b
  advance : ∀ k, a < x k → x k < b → x k + η ≤ x (k + 1)

private theorem integer_propagate (P : ℤ → Prop)
    (step : ∀ k, P k → P (k + 1)) {i j : ℤ} (hij : i ≤ j) (hi : P i) : P j := by
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  clear hij
  induction n with
  | zero => simpa using hi
  | succ n ih => simpa only [Nat.cast_succ, add_assoc] using step (i + n) ih

namespace ScalarBandProgress

variable {x : ℤ → ℝ} {a b η : ℝ} (h : ScalarBandProgress x a b η)

include h

private theorem above_forward {i j : ℤ} (hij : i ≤ j) (hi : a < x i) : a < x j :=
  integer_propagate (fun k => a < x k)
    (fun k hk => lt_of_not_ge (fun hk' => (not_le_of_gt hk) (h.lower_back k hk'))) hij hi

private theorem upper_forward_le {i j : ℤ} (hij : i ≤ j) (hi : b ≤ x i) : b ≤ x j :=
  integer_propagate (fun k => b ≤ x k) h.upper_forward hij hi

private theorem between_markers {i j k : ℤ}
    (hi : i ∈ bandMarkers x a b) (hj : j ∈ bandMarkers x a b)
    (hik : i ≤ k) (hkj : k ≤ j) : k ∈ bandMarkers x a b := by
  refine ⟨h.above_forward hik hi.1, ?_⟩
  by_contra hk
  exact (not_le_of_gt hj.2) (h.upper_forward_le hkj (le_of_not_gt hk))

private theorem accumulated_advance {i : ℤ} (n : ℕ)
    (hm : ∀ k, i ≤ k → k < i + n → k ∈ bandMarkers x a b) :
    x i + (n : ℝ) * η ≤ x (i + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : i + (n : ℤ) < i + ((n + 1 : ℕ) : ℤ) := by omega
    have hk := hm (i + n) (by omega) hn
    have hp := ih (fun k hl hu => hm k hl (by omega))
    have hs := h.advance (i + n) hk.1 hk.2
    push_cast
    push_cast at hs
    rw [add_assoc] at hs
    linarith

private theorem marker_span (hη : 0 < η) (N : ℕ) (hN : b - a < (N : ℝ) * η)
    {i j : ℤ} (hi : i ∈ bandMarkers x a b) (hj : j ∈ bandMarkers x a b)
    (hij : i ≤ j) : j - i < (N : ℤ) := by
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  have hp := h.accumulated_advance n (fun k hk hk' =>
    h.between_markers hi hj hk (by omega))
  by_contra hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hmul := mul_le_mul_of_nonneg_right hnn hη.le
  have hwidth : (n : ℝ) * η < b - a := by
    have := hi.1
    have := hj.2
    linarith
  linarith

/-- A bi-infinite sequence with local cap barriers and positive middle progress
has a finite marker set. It is entirely in one cap, or its markers form one
integer interval of span less than `N`, with lower and upper tails. -/
theorem classify (hη : 0 < η) (N : ℕ) (hN : b - a < (N : ℝ) * η) :
    (bandMarkers x a b).Finite ∧
      ((∀ k, x k ≤ a) ∨ (∀ k, b ≤ x k) ∨
        ∃ l r : ℤ, l ≤ r ∧ r - l < (N : ℤ) ∧
          bandMarkers x a b = Set.Icc l r ∧
          (∀ k, k < l → x k ≤ a) ∧ (∀ k, r < k → b ≤ x k)) := by
  classical
  by_cases hm : (bandMarkers x a b).Nonempty
  · obtain ⟨i, hi⟩ := hm
    have hf : (bandMarkers x a b).Finite := by
      apply (Set.finite_Icc (i - N) (i + N)).subset
      intro j hj
      by_cases hij : i ≤ j
      · have := h.marker_span hη N hN hi hj hij
        exact ⟨by omega, by omega⟩
      · have := h.marker_span hη N hN hj hi (by omega)
        exact ⟨by omega, by omega⟩
    obtain ⟨l, hl, hmin⟩ := Set.exists_min_image _ (fun k : ℤ => k) hf ⟨i, hi⟩
    obtain ⟨r, hr, hmax⟩ := Set.exists_max_image _ (fun k : ℤ => k) hf ⟨i, hi⟩
    refine ⟨hf, Or.inr (Or.inr ⟨l, r, hmin r hr,
      h.marker_span hη N hN hl hr (hmin r hr), ?_, ?_, ?_⟩)⟩
    · ext k
      exact ⟨fun hk => ⟨hmin k hk, hmax k hk⟩,
        fun hk => h.between_markers hl hr hk.1 hk.2⟩
    · intro k hk
      by_contra ha
      have hb : x k < b := by
        by_contra hb
        exact (not_le_of_gt hl.2) (h.upper_forward_le hk.le (le_of_not_gt hb))
      have := hmin k ⟨lt_of_not_ge ha, hb⟩
      change l ≤ k at this
      omega
    · intro k hk
      by_contra hb
      have ha := h.above_forward hk.le hr.1
      have := hmax k ⟨ha, lt_of_not_ge hb⟩
      change k ≤ r at this
      omega
  · have empty : ∀ k, ¬ (a < x k ∧ x k < b) := fun k hk => hm ⟨k, hk⟩
    have hf : (bandMarkers x a b).Finite := by
      have he : bandMarkers x a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hm
      rw [he]
      exact Set.finite_empty
    refine ⟨hf, ?_⟩
    by_cases hl : ∃ i, x i ≤ a
    · obtain ⟨i, hi⟩ := hl
      apply Or.inl
      intro k
      by_cases hki : k ≤ i
      · by_contra hk
        exact (not_le_of_gt (h.above_forward hki (lt_of_not_ge hk))) hi
      · exact integer_propagate (fun j => x j ≤ a) (fun j hj => by
          by_contra hj'
          exact empty (j + 1) ⟨lt_of_not_ge hj', h.no_jump j hj⟩) (by omega) hi
    · apply Or.inr ∘ Or.inl
      intro k
      have hk : a < x k := lt_of_not_ge (fun hk => hl ⟨k, hk⟩)
      exact le_of_not_gt (fun hb => empty k ⟨hk, hb⟩)

end ScalarBandProgress
end D5.S1.Dynamics.Shadowing
