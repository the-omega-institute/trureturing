/- GID: D5/S3/Quantum/Tomography/RootTubeStrongUnextendibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/RootTubeStrongUnextendibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete residual-tube coverage and a two-relation no-partner certificate quantitatively exclude a six-frame together with even one additional common-unbiased vector. -/

import D5.S3.Quantum.Tomography.CompleteRootSupergraphExclusion

/- Reuse audit (2026-09-07):
   * Reuses Matrix.trace and the same matrix-valued tubes and one-sided overlap
     relations as CompleteRootSupergraphExclusion. No new ray, Hadamard,
     context, interval, graph, or frame-potential carrier is introduced.
   * The older consumer excludes two six-frames using partner-graph coloring.
     This result consumes the stronger, concretely checked empty-partner
     condition and excludes one additional vector. It does not infer the
     finite condition from an external PASS or omit the full tube cover.
   * Rank-one outer products of normalized vectors are the intended instance.
     The algebraic statement deliberately needs only the listed trace bounds.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.RootTubeStrongUnextendibility

open Matrix

/-- A quantitative strong-unextendibility consumer. Every possible first
six-clique has an empty common unbiased-neighbor set. Thus any further point
in the complete tube cover has a cross-unbiasedness error at least tau.

The tubes may be empty, overlapping, or contain multiple roots. A refined tube
cover is admissible only after all residual-sublevel points have been proved
retained by that refinement. Root counts and JSON reports are not premises.

For an actual complete third basis and a rank-one projector for a proposed
fourth vector, this excludes a (6,6,6,1) MUB constellation relative to the two
fixed bases once the residual and interval hypotheses are instantiated. -/
theorem six_frame_has_cross_error_to_any_covered_point
    {κ : Type*}
    (tube : κ → Set (Matrix (Fin 6) (Fin 6) ℂ))
    (orthogonalCandidate unbiasedCandidate : κ → κ → Prop)
    (η μ τ : ℝ) (hημ : η ≤ μ)
    (hSame : ∀ k P ∈ tube k, ∀ Q ∈ tube k,
      μ ≤ (trace (P * Q)).re)
    (hOrth : ∀ k l, k ≠ l → ∀ P ∈ tube k, ∀ Q ∈ tube l,
      (trace (P * Q)).re < η → orthogonalCandidate k l)
    (hUnbiased : ∀ k l, ∀ P ∈ tube k, ∀ Q ∈ tube l,
      |(trace (P * Q)).re - (1 / 6 : ℝ)| < τ →
        unbiasedCandidate k l)
    (hNoPartner : ∀ c : Fin 6 → κ, Function.Injective c →
      (∀ i j, i ≠ j → orthogonalCandidate (c i) (c j)) →
      ∀ l, ∃ i, ¬ unbiasedCandidate (c i) l)
    (C : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
    (Q : Matrix (Fin 6) (Fin 6) ℂ)
    (hCoverC : ∀ i, ∃ k, C i ∈ tube k)
    (hCoverQ : ∃ k, Q ∈ tube k)
    (hSmallC : ∀ i j, i ≠ j → (trace (C i * C j)).re < η) :
    ∃ i, τ ≤ |(trace (C i * Q)).re - (1 / 6 : ℝ)| := by
  classical
  choose c hc using hCoverC
  obtain ⟨l, hl⟩ := hCoverQ
  have hci : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hj : C j ∈ tube (c i) := by rw [hij]; exact hc j
    have hlo := hSame (c i) (C i) (hc i) (C j) hj
    exact (not_lt_of_ge (le_trans hημ hlo)) (hSmallC i j hne)
  have hClique : ∀ i j, i ≠ j → orthogonalCandidate (c i) (c j) := by
    intro i j hij
    exact hOrth (c i) (c j) (hci.ne hij)
      (C i) (hc i) (C j) (hc j) (hSmallC i j hij)
  obtain ⟨i, hi⟩ := hNoPartner c hci hClique l
  refine ⟨i, ?_⟩
  by_contra hnot
  exact hi (hUnbiased (c i) l (C i) (hc i) Q hl (lt_of_not_ge hnot))

#print axioms six_frame_has_cross_error_to_any_covered_point

end D5.S3.Quantum.Tomography.RootTubeStrongUnextendibility
