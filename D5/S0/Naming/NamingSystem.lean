/- GID: D5/S0/Naming/NamingSystem
   generality: G
   mirror-B: D5/B/S0/Naming/NamingSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Countable naming systems over uncountable carriers have null named image. -/

import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

namespace D5.S0.Naming

open MeasureTheory

universe u v w

/-- A naming system consists of a partial assignment from names into a measured carrier,
together with finite height sublevels. -/
structure NamingSystem (X : Type u) [MeasureSpace X] where
  Name : Type v
  assignment : Name → Option X
  height : Name → ℕ
  finite_layer : ∀ Q, Set.Finite {n | height n ≤ Q}

namespace NamingSystem

/-- Names available by height `Q`. -/
def layer {X : Type u} [MeasureSpace X] (system : NamingSystem X) (Q : ℕ) :
    Set system.Name :=
  {n | system.height n ≤ Q}

/-- Points reached by the partial assignment. -/
def named {X : Type u} [MeasureSpace X] (system : NamingSystem X) : Set X :=
  {x | ∃ n, system.assignment n = some x}

end NamingSystem

/-- The finite height layers exhaust the name type, so the names are countable. -/
theorem name_layer_finite {X : Type u} [MeasureSpace X] (system : NamingSystem X) :
    Countable system.Name := by
  rw [← Set.countable_univ_iff]
  have h_cover : ⋃ Q : ℕ, system.layer Q = Set.univ :=
    Set.iUnion_eq_univ_iff.mpr fun n => ⟨system.height n, by simp [NamingSystem.layer]⟩
  rw [← h_cover]
  exact Set.countable_iUnion fun Q => by
    simpa [NamingSystem.layer] using (system.finite_layer Q).countable

/-- A naming system reaches only countably many carrier points. -/
theorem named_countable {X : Type u} [MeasureSpace X] (system : NamingSystem X) :
    system.named.Countable := by
  letI : Countable system.Name := name_layer_finite system
  have h_range : (Set.range system.assignment).Countable := Set.countable_range _
  have h_preimage := h_range.preimage (Option.some_injective X)
  refine h_preimage.mono ?_
  rintro x ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- A countable family of naming systems has null named image under an atomless,
sigma-finite measure on an uncountable carrier. -/
theorem dark_side_conservation
    {X : Type u} [MeasureSpace X] [Uncountable X]
    [NoAtoms (volume : Measure X)] [SigmaFinite (volume : Measure X)]
    {J : Type w} [Countable J] (systems : J → NamingSystem X) :
    volume (⋃ j, (systems j).named) = 0 := by
  exact (Set.countable_iUnion fun j => named_countable (systems j)).measure_zero volume

end D5.S0.Naming
