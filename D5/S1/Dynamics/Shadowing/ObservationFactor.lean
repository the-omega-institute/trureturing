/- GID: D5/S1/Dynamics/Shadowing/ObservationFactor
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous observation names give a surjective factor onto a shift-invariant language. -/

import D5.S1.Dynamics.Shadowing.CompactObservationSubshift

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/-- The left shift on the complete observation language. -/
def observationLanguageShift {X : Type u} {A : Type v}
    (f : X → X) (a : X → A) :
    observationLanguage f a → observationLanguage f a := fun w =>
  ⟨(fun n => w.val (n + 1)), observationLanguage_shift_invariant f a w.property⟩

/-- The complete observation name, viewed as a point of its image language. -/
def observationNameFactor {X : Type u} {A : Type v}
    (f : X → X) (a : X → A) : X → observationLanguage f a := fun x =>
  ⟨(fun n => a (f^[n] x)), ⟨x, rfl⟩⟩

/-- A continuous observation is a surjective semiconjugacy from the source
dynamics to the shift on its complete observation language.  This packages
the range construction and the shift-invariance lemma as a genuine
topological factor map. -/
theorem observationFactor_continuous_surjective_semiconj
    {X : Type u} {A : Type v}
    [TopologicalSpace X] [TopologicalSpace A]
    (f : X → X) (a : X → A) (hf : Continuous f) (ha : Continuous a) :
    Continuous (observationNameFactor f a) ∧
      Surjective (observationNameFactor f a) ∧
        Semiconj (observationNameFactor f a) f (observationLanguageShift f a) := by
  have hname : Continuous (fun x n => a (f^[n] x)) :=
    continuous_observationName f a hf ha
  have hfactor : Continuous (observationNameFactor f a) :=
    hname.subtype_mk _
  have hsurj : Surjective (observationNameFactor f a) := by
    intro w
    rcases w.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  have hsem : Semiconj (observationNameFactor f a) f
      (observationLanguageShift f a) := by
    intro x
    apply Subtype.ext
    funext n
    change a (f^[n] (f x)) = a (f^[n + 1] x)
    rw [Function.iterate_succ_apply]
  exact ⟨hfactor, hsurj, hsem⟩

#print axioms observationFactor_continuous_surjective_semiconj

end D5.S1.Dynamics.Shadowing
