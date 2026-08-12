/- GID: D5/S0/Naming/GraphPairingCriterion
   generality: G
   mirror-B: D5/B/S0/Naming/GraphPairingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Graph pairing separation is injectivity plus a subsingleton range complement. -/

import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Subsingleton

namespace D5.S0.Naming.GraphPairingCriterion

open Set

universe u v

/-- The Boolean-valued graph pairing of `f` separates both curried coordinates exactly when
`f` is injective and its range omits at most one codomain point. -/
theorem graph_pairing_separating_iff {A : Type u} {B : Type v} (f : A -> B) :
    Function.Injective (fun a => fun b => f a = b) /\
        Function.Injective (fun b => fun a => f a = b) <->
      Function.Injective f /\ (Set.range f)ᶜ.Subsingleton := by
  constructor
  · rintro ⟨rowInjective, columnInjective⟩
    constructor
    · intro a a' haa'
      apply rowInjective
      funext b
      simp only [haa']
    · intro b hb b' hb'
      apply columnInjective
      funext a
      apply propext
      constructor
      · intro hfa
        exact (hb ⟨a, hfa⟩).elim
      · intro hfa
        exact (hb' ⟨a, hfa⟩).elim
  · rintro ⟨hf, outsideSubsingleton⟩
    constructor
    · intro a a' hrows
      apply hf
      have hpoint : (f a = f a') ↔ (f a' = f a') :=
        Iff.of_eq (congrFun hrows (f a'))
      exact hpoint.mpr rfl
    · intro b b' hcolumns
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, ha⟩ := hb
        have hpoint : (f a = b) ↔ (f a = b') :=
          Iff.of_eq (congrFun hcolumns a)
        exact ha.symm.trans (hpoint.mp ha)
      · by_cases hb' : b' ∈ Set.range f
        · obtain ⟨a, ha⟩ := hb'
          have hpoint : (f a = b) ↔ (f a = b') :=
            Iff.of_eq (congrFun hcolumns a)
          exact (hpoint.mpr ha).symm.trans ha
        · exact outsideSubsingleton hb hb'

/-- Checked evidence that the quantified domains can be inhabited. -/
example : Unit := ()

/-- The identity on a singleton witnesses simultaneous row and column separation and an empty
range complement. -/
example :
    Function.Injective (fun a : Unit => fun b : Unit => a = b) /\
      Function.Injective (fun b : Unit => fun a : Unit => a = b) := by
  constructor <;> intro x y _ <;> exact Subsingleton.elim x y

end D5.S0.Naming.GraphPairingCriterion
