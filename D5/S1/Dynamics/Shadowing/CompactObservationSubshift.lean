/- GID: D5/S1/Dynamics/Shadowing/CompactObservationSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/CompactObservationSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact continuous finite observations form closed shift-invariant sofic languages. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/-- The complete one-sided observation name of a source point. -/
def observationLanguage {X : Type u} {A : Type v} (f : X → X) (a : X → A) :
    Set (ℕ → A) :=
  Set.range (fun x n => a (f^[n] x))

/-- The observation-name map is continuous when the source dynamics and
readout are continuous.  This is the product-topology input for compactness. -/
theorem continuous_observationName {X : Type u} {A : Type v}
    [TopologicalSpace X] [TopologicalSpace A]
    (f : X → X) (a : X → A) (hf : Continuous f) (ha : Continuous a) :
    Continuous (fun x n => a (f^[n] x)) := by
  exact continuous_pi fun n => ha.comp (hf.iterate n)

/-- A compact continuous source has a compact, hence closed, observation
language in the product of its finite discrete observation alphabet. -/
theorem observationLanguage_isCompact_isClosed {X : Type u} {A : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (f : X → X) (a : X → A) (hf : Continuous f) (ha : Continuous a) :
    IsCompact (observationLanguage f a) ∧ IsClosed (observationLanguage f a) := by
  have hcont : Continuous (fun x n => a (f^[n] x)) :=
    continuous_observationName f a hf ha
  have hcompact : IsCompact (observationLanguage f a) := by
    exact isCompact_range hcont
  exact ⟨hcompact, hcompact.isClosed⟩

/-- Shifting an observation name by one step is again an observation name.
This is the dynamical factor law that turns the compact image into a subshift. -/
theorem observationLanguage_shift_invariant {X : Type u} {A : Type v}
    (f : X → X) (a : X → A) {w : ℕ → A}
    (hw : w ∈ observationLanguage f a) :
    (fun n => w (n + 1)) ∈ observationLanguage f a := by
  rcases hw with ⟨x, rfl⟩
  refine ⟨f x, ?_⟩
  funext n
  simp only [Function.iterate_succ_apply]

/-- Under shadowing, the compact observation language is simultaneously a
finite graph language, compact/closed, and shift-invariant. -/
theorem compact_observation_is_closed_shift_invariant_sofic
    {X : Type u} {A : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (f : X → X) (a : X → A) (hf : Continuous f) (ha : Continuous a)
    (hs : HasShadowing f) :
    IsSofic (observationLanguage f a) ∧
      IsClosed (observationLanguage f a) ∧
      ∀ w ∈ observationLanguage f a,
        (fun n => w (n + 1)) ∈ observationLanguage f a := by
  have hsofic : IsSofic (observationLanguage f a) := by
    exact finite_observation_isSofic f a ha hs
  have hcompactClosed := observationLanguage_isCompact_isClosed f a hf ha
  refine ⟨?_, hcompactClosed.2, ?_⟩
  · simpa only [observationLanguage] using hsofic
  · intro w hw
    exact observationLanguage_shift_invariant f a hw

#print axioms continuous_observationName
#print axioms observationLanguage_isCompact_isClosed
#print axioms observationLanguage_shift_invariant
#print axioms compact_observation_is_closed_shift_invariant_sofic

end D5.S1.Dynamics.Shadowing
