/- GID: D5/S1/Dynamics/Shadowing/ExactExpansiveConjugacy
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ExactExpansiveConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport of exact positively expansive maps along compact metric homeomorphisms. -/

import D5.S1.Dynamics.Shadowing.ExactPendantObstruction

/-! A homeomorphism carries exact dynamics and transports the all-time separation radius. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set

namespace D5.S1.Dynamics.Shadowing.ExactExpansiveConjugacy

open ExactPendantObstruction (TopologicallyExact)

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]

/-- The conjugate of an exact map with singleton forward Bowen sets has the same
properties, with a radius supplied by uniform continuity of the inverse homeomorphism. -/
theorem exact_expansive_conjugate (e : X ≃ₜ Y) {f : X → X}
    (hf : Continuous f) (hex : TopologicallyExact f)
    (hB : ∃ ε > 0, ForwardBowenBound f univ ε 1) :
    let g := e ∘ f ∘ e.symm
    Continuous g ∧ TopologicallyExact g ∧ PositivelyExpansive g := by
  let g : Y → Y := e ∘ f ∘ e.symm
  have hconj : Semiconj e f g := by
    intro x
    simp [g]
  refine ⟨e.continuous.comp (hf.comp e.symm.continuous), ?_, ?_⟩
  · intro U hU hU'
    have hpre : (e ⁻¹' U).Nonempty := by
      obtain ⟨y, hy⟩ := hU'
      exact ⟨e.symm y, by simpa using hy⟩
    obtain ⟨n, hn, hcover⟩ := hex (e ⁻¹' U) (hU.preimage e.continuous) hpre
    refine ⟨n, hn, Set.eq_univ_of_forall ?_⟩
    intro y
    have hy : e.symm y ∈ f^[n] '' (e ⁻¹' U) := by rw [hcover]; exact mem_univ _
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨e x, hx, ?_⟩
    rw [← hconj.iterate_right n x, hxy, e.apply_symm_apply]
  · obtain ⟨ε, hε, hBε⟩ := hB
    obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous e.symm.continuous)) ε hε
    refine ⟨δ, hδ, fun x y hclose => ?_⟩
    have hsymm : Semiconj e.symm g f := by
      intro z
      simp [g]
    let a := e.symm x
    let b := e.symm y
    have hb : b ∈ ForwardBowen f ε a := by
      intro n
      change dist (f^[n] (e.symm x)) (f^[n] (e.symm y)) < ε
      rw [← hsymm.iterate_right n x, ← hsymm.iterate_right n y]
      exact hcontrol (hclose n)
    have ha : a ∈ ForwardBowen f ε a := fun n => by simpa using hε
    have htwo : ({a, b} : Set X) ⊆ univ ∩ ForwardBowen f ε a := by
      intro z hz
      have hz' : z = a ∨ z = b := by simpa using hz
      rcases hz' with rfl | rfl
      · exact ⟨mem_univ _, ha⟩
      · exact ⟨mem_univ _, hb⟩
    apply e.symm.injective
    by_contra hab
    have hc := (Set.encard_mono htwo).trans (hBε a (mem_univ _))
    rw [Set.encard_pair hab] at hc
    exact (by decide : ¬ (2 : ℕ∞) ≤ 1) hc

#print axioms exact_expansive_conjugate

end D5.S1.Dynamics.Shadowing.ExactExpansiveConjugacy
