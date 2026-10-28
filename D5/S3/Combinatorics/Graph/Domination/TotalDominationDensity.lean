/- GID: D5/S3/Combinatorics/Graph/Domination/TotalDominationDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TotalDominationDensity
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Actual total-domination roots approximate logarithmic complex targets. -/

import D5.S3.Combinatorics.Graph.Domination.TotalDominationApproximation

/-! The original issue 23313 target uses actual finite simple graphs and actual total subsets.
Known cone, friendship and independent-fibre formulas are consumed ingredients.
No ordinary-domination or conditional density premise is used. -/

set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.Domination.TotalDominationDensity

open Complex
open D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds
open D5.S3.Combinatorics.Graph.Domination.TotalDominationBlowup
open D5.S3.Combinatorics.Graph.Domination.TotalDominationApproximation

/-- The seed and exponent are selected jointly for every nonzero logarithmic radius. -/
theorem roots_approximate_exp_nonunit (ξ : ℂ) (hξ : ξ.re ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℂ),
      2 ≤ n ∧ (∀ v, ∃ u, G.Adj v u) ∧ complexPolynomial G ≠ 0 ∧
      (complexPolynomial G).IsRoot w ∧ ‖w - (Complex.exp ξ - 1)‖ < ε := by
  obtain ⟨N, hN⟩ := joint_power_root_approximation ξ hξ ε hε
  have hseed : ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r t α : ℝ),
      2 ≤ n ∧ (∀ v, ∃ u, G.Adj v u) ∧ (complexPolynomial G).IsRoot (r : ℂ) ∧
      (N : ℝ) + 2 < t / ξ.re ∧
      Complex.exp ((t : ℂ) + (α : ℂ) * I) = (1 + r : ℝ) := by
    by_cases hpos : 0 < ξ.re
    · let L : ℝ := ((N : ℝ) + 3) * ξ.re
      let R : ℝ := Real.exp L + 2
      obtain ⟨n, G, r, hn, hr, hni, _, hz⟩ := labelled_unbounded_negative_roots R
        (by dsimp [R]; linarith [Real.exp_pos L])
      let q : ℝ := -(1 + r)
      have hq : 0 < q := by dsimp [q, R] at *; linarith [Real.exp_pos L]
      have hqL : Real.exp L < q := by dsimp [q, R] at *; linarith
      have ht : L < Real.log q := by
        have hh := Real.log_lt_log (Real.exp_pos L) hqL
        rwa [Real.log_exp] at hh
      refine ⟨n, G, r, Real.log q, Real.pi, hn, hni, hz, ?_, ?_⟩
      · apply (lt_div_iff₀ hpos).mpr
        dsimp [L] at ht
        nlinarith
      · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hq,
          Complex.exp_pi_mul_I]
        dsimp [q]
        push_cast
        ring
    · have hneg : ξ.re < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hξ
      let L : ℝ := ((N : ℝ) + 3) * ξ.re
      obtain ⟨n, G, r, hn, hni, _, hz, hr, hclose⟩ :=
        complex_seed_accumulation (Real.exp L) (Real.exp_pos L)
      have hsmall : 1 + r < Real.exp L := by
        have he : (r : ℂ) - (-1 : ℂ) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
        simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hclose
      have ht : Real.log (1 + r) < L := by
        have hh := Real.log_lt_log hr hsmall
        rwa [Real.log_exp] at hh
      refine ⟨n, G, r, Real.log (1 + r), 0, hn, hni, hz, ?_, ?_⟩
      · apply (lt_div_iff_of_neg hneg).mpr
        dsimp [L] at ht
        nlinarith
      · simp only [Complex.ofReal_zero, zero_mul, add_zero]
        rw [← Complex.ofReal_exp, Real.exp_log hr]
  obtain ⟨n, G, r, t, α, hn, hni, hz, ht, he⟩ := hseed
  obtain ⟨k, u, hk, hu, hclose⟩ := hN t α ht
  obtain ⟨m, H, hm, hnzH, hniH, hroots⟩ := labelled_root_blowup n G hn hni (r : ℂ) hz k hk
  refine ⟨m, H, u - 1, hm, hniH, hnzH, ?_, ?_⟩
  · apply hroots
    have hh : 1 + (u - 1) = u := by ring
    rw [hh, hu, he]
    push_cast
    ring
  · have hh : (u - 1) - (Complex.exp ξ - 1) = u - Complex.exp ξ := by ring
    rwa [hh]

#print axioms roots_approximate_exp_nonunit

end D5.S3.Combinatorics.Graph.Domination.TotalDominationDensity
