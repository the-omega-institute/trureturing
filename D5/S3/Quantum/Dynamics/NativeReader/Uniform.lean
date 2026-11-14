/- GID: D5/S3/Quantum/Dynamics/NativeReader/Uniform
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Uniform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform punctured-parameter nonvanishing along the actual fifteen pulses. -/

import D5.S3.Quantum.Dynamics.NativeReader.Invariants

/-! One parameter neighborhood works for both complete auxiliary sectors and all internal times. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

open Matrix Filter Set
open scoped Topology

/-- The literal source pulse entrance, rather than an assumed invariant certificate,
    supplies a nonzero analytic charge at the mathematical reference parameter. -/
theorem entranceCharge_punctured (i a : Bool) (k : Fin 15) :
    ∀ᶠ lam in 𝓝[≠] alpha, entranceCharge i a k lam ≠ 0 := by
  rcases (entranceCharge_analytic i a k alpha).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have ha : AnalyticOnNhd ℝ (entranceCharge i a k) univ :=
      fun t _ => entranceCharge_analytic i a k t
    have he := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ alpha) (h.filter_mono nhdsWithin_le_nhds).frequently
    exact False.elim (entranceCharge_at_zero i a k (he (mem_univ 0)))
  · exact h

private theorem current_nonzero_of_charges (lam : ℝ)
    (hc : ∀ (i a : Bool) (k : Fin 15), entranceCharge i a k lam ≠ 0) :
    ∀ (i : Bool) (k : Fin 15) (s : ℝ), during i lam k s (readyTail i) ≠ 0 := by
  have step (i : Bool) (k : Fin 15) (h : entrance i lam k (readyTail i) ≠ 0) (s : ℝ) :
      during i lam k s (readyTail i) ≠ 0 := by
    by_cases hj : address k = 1 ∨ address k = 3
    · obtain ⟨a, ha⟩ : ∃ a : Bool, address k = changedAddress a := by
        rcases hj with hj | hj
        · exact ⟨false, hj⟩
        · exact ⟨true, hj⟩
      have hn := pair_current_nonzero a (pairVector i a (entrance i lam k))
        (hc i a k) (angle lam (address k) * s)
      rw [← pulse_pair, pairVector, edge_ready] at hn
      simpa only [during, ha] using hn
    · simpa only [during, unchanged_current i (address k) (not_or.mp hj)] using
        mul_ne_zero (show
          (if address k = 0 ∧ i = true then unitPhase (angle lam (address k) * s) ^ 2
          else unitPhase (angle lam (address k) * s)) ≠ 0 by
            split_ifs <;> simp [unitPhase, Complex.exp_ne_zero]) h
  have ent (i : Bool) (k : ℕ) (hk : k ≤ 15) : entrance i lam k (readyTail i) ≠ 0 := by
    induction k with
    | zero => simp [entrance, readyVector]
    | succ k ih =>
      have hn := step i ⟨k, by omega⟩ (ih (by omega)) 1
      simpa only [during_right] using hn
  intro i k s
  exact step i k (ent i k (by omega)) s

/-- Uniform in sector, actual pulse entrance, and every internal time, including seams.
    The parameter zero is only used in the proof of charge nonidentity. -/
theorem reader_uniform_nonvanishing :
    ∃ eta : ℝ, 0 < eta ∧ eta < min alpha (2 * Real.pi - alpha) ∧
      ∀ lam : ℝ, 0 < |lam - alpha| → |lam - alpha| < eta →
        ∀ (i : Bool) (k : Fin 15) (s : ℝ),
          during i lam k s (readyTail i) ≠ 0 := by
  have he : ∀ᶠ lam in 𝓝[≠] alpha,
      ∀ (i a : Bool) (k : Fin 15), entranceCharge i a k lam ≠ 0 := by
    simp only [Filter.eventually_all]
    exact entranceCharge_punctured
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp he
  have halpha : 0 < min alpha (2 * Real.pi - alpha) := by
    unfold alpha
    exact lt_min (by positivity) (by linarith [Real.pi_pos])
  let eta := min eps (min alpha (2 * Real.pi - alpha)) / 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hsmall : eta < min alpha (2 * Real.pi - alpha) := by
    dsimp [eta]
    linarith [min_le_right eps (min alpha (2 * Real.pi - alpha))]
  refine ⟨eta, heta, hsmall, ?_⟩
  intro lam hne hlt
  have hdist : dist lam alpha < eps := by
    rw [Real.dist_eq]
    have hm := min_le_left eps (min alpha (2 * Real.pi - alpha))
    dsimp [eta] at hlt
    linarith
  exact current_nonzero_of_charges lam (hball hdist (by
    change lam ≠ alpha
    exact sub_ne_zero.mp (abs_pos.mp hne)))

end D5.S3.Quantum.Dynamics.NativeReader
