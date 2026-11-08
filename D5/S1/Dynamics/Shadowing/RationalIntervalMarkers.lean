/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalMarkers
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalMarkers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-marker classification for closed rational interval pseudo-orbits. -/

import D5.S1.Dynamics.Shadowing.BiInfiniteBand
import Mathlib.Order.Interval.Set.Card

/-! Closed rational pseudo-orbits have bounded consecutive middle markers. -/

namespace D5.S1.Dynamics.Shadowing

/-- The rational north-south interval map, evaluated as a real function. -/
noncomputable def rationalIntervalMap (u : ℝ) : ℝ := 2 * u / (1 + u)

/-- Closed errors at every integer time, with every coordinate in the closed unit interval. -/
def ClosedRationalPseudoOrbit (δ : ℝ) (x : ℤ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℤ, |rationalIntervalMap (x k) - (x (k + 1) : ℝ)| ≤ δ

private theorem rational_step_bounds {u v δ : ℝ} (hu : 0 ≤ u)
    (hδ : δ ≤ 1 / 256) (he : |rationalIntervalMap u - v| ≤ δ) :
    ((1 / 3 : ℝ) ≤ u → 1 / 3 < v) ∧
    ((2 / 3 : ℝ) ≤ u → 2 / 3 < v) ∧
    (u ≤ (1 / 3 : ℝ) → v < 2 / 3) ∧
    ((1 / 3 : ℝ) ≤ u → u ≤ 2 / 3 → u + 1 / 8 < v) := by
  have hd : 0 < 1 + u := by linarith
  obtain ⟨hel, heu⟩ := abs_le.mp he
  constructor
  · intro ha
    have hf : (1 / 2 : ℝ) ≤ rationalIntervalMap u := by
      apply (le_div_iff₀ hd).2
      linarith
    linarith
  constructor
  · intro hb
    have hf : (4 / 5 : ℝ) ≤ rationalIntervalMap u := by
      apply (le_div_iff₀ hd).2
      linarith
    linarith
  constructor
  · intro ha
    have hf : rationalIntervalMap u ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hd).2
      linarith
    linarith
  · intro ha hb
    have hfactor : 0 ≤ (2 / 3 - u) * (15 * u - 3) :=
      mul_nonneg (by linarith) (by linarith)
    have hf : u + 2 / 15 ≤ rationalIntervalMap u := by
      apply (le_div_iff₀ hd).2
      nlinarith
    linarith

/-- Every closed-error pseudo-orbit at scale at most `1/256` has at most three
consecutive middle markers, or lies strictly in one cap. Boundary coordinates
force a marker at the indicated adjacent integer time. -/
theorem rational_interval_marker_classification {δ : ℝ}
    (hδ : δ ≤ 1 / 256) (x : ℤ → Set.Icc (0 : ℝ) 1)
    (hx : ClosedRationalPseudoOrbit δ x) :
    let B := bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3)
    B.Finite ∧ B.ncard ≤ 3 ∧
      ((∀ k, (x k : ℝ) < 1 / 3) ∨ (∀ k, (2 / 3 : ℝ) < x k) ∨
        ∃ l r : ℤ, l ≤ r ∧ r - l ≤ 2 ∧ B = Set.Icc l r ∧
          (∀ k, k < l → (x k : ℝ) ≤ 1 / 3) ∧
          (∀ k, r < k → (2 / 3 : ℝ) ≤ x k)) ∧
      (∀ k, (x k : ℝ) = 1 / 3 → k + 1 ∈ B) ∧
      (∀ k, (x k : ℝ) = 2 / 3 → k - 1 ∈ B) := by
  dsimp only
  have step (k : ℤ) := rational_step_bounds (x k).property.1 hδ (hx k)
  have hbar : ScalarBandProgress (fun k => (x k : ℝ)) (1 / 3) (2 / 3) (1 / 8) := by
    constructor
    · intro k hk
      by_contra ha
      exact (not_le_of_gt ((step k).1 (le_of_lt (lt_of_not_ge ha)))) hk
    · intro k hk
      exact ((step k).2.1 hk).le
    · intro k hk
      exact (step k).2.2.1 hk
    · intro k ha hb
      exact ((step k).2.2.2 ha.le hb.le).le
  have low_boundary (k : ℤ) (hk : (x k : ℝ) = 1 / 3) :
      k + 1 ∈ bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3) := by
    exact ⟨(step k).1 (by rw [hk]), (step k).2.2.1 (by rw [hk])⟩
  have high_boundary (k : ℤ) (hk : (x k : ℝ) = 2 / 3) :
      k - 1 ∈ bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3) := by
    have hs := step (k - 1)
    have he : k - 1 + 1 = k := by omega
    rw [he] at hs
    constructor
    · by_contra ha
      have hh := hs.2.2.1 (le_of_not_gt ha)
      rw [hk] at hh
      exact (lt_irrefl _) hh
    · by_contra hb
      have hh := hs.2.1 (le_of_not_gt hb)
      rw [hk] at hh
      exact (lt_irrefl _) hh
  obtain ⟨hf, hc⟩ := hbar.classify (by norm_num) 3 (by norm_num)
  have hcard : (bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3)).ncard ≤ 3 := by
    rcases hc with hl | hu | ⟨l, r, _, hspan, heq, _, _⟩
    · have heq : bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro k hk
        exact (not_lt_of_ge (hl k)) hk.1
      rw [heq]
      simp
    · have heq : bandMarkers (fun k => (x k : ℝ)) (1 / 3) (2 / 3) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro k hk
        exact (not_lt_of_ge (hu k)) hk.2
      rw [heq]
      simp
    · rw [heq, Set.ncard_Icc, Int.card_Icc]
      omega
  refine ⟨hf, hcard, ?_, low_boundary, high_boundary⟩
  rcases hc with hl | hu | ⟨l, r, hlr, hspan, heq, hleft, hright⟩
  · left
    intro k
    refine lt_of_le_of_ne (hl k) ?_
    intro hk
    exact (not_lt_of_ge (hl (k + 1))) (low_boundary k hk).1
  · right; left
    intro k
    refine lt_of_le_of_ne (hu k) ?_
    intro hk
    exact (not_lt_of_ge (hu (k - 1))) (high_boundary k hk.symm).2
  · exact Or.inr (Or.inr ⟨l, r, hlr, by omega, heq, hleft, hright⟩)

end D5.S1.Dynamics.Shadowing
