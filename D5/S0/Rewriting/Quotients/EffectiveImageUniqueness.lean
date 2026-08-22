/- GID: D5/S0/Rewriting/Quotients/EffectiveImageUniqueness
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/EffectiveImageUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A descended map is fixed on the effective image and globally unique under surjectivity. -/

import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-21):
   * Exact pinned-Mathlib hit: `Function.Surjective.injective_comp_right`
     proves global uniqueness after right composition by a surjection.
   * Exact pinned-Mathlib hit: `Set.eqOn_range` identifies agreement on the
     effective image with equality after right composition by the readout.
   * Repository search found `DynamicsDescent.dynamics_descends_iff`, which
     gives adjacent existence and uniqueness for a surjective self-map
     quotient, but not the general effective-image statement below.
-/

namespace D5.S0.Rewriting.Quotients.EffectiveImageUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Two maps making the process/readout square commute agree on the effective
image. Surjectivity promotes this to global uniqueness; without surjectivity,
the commuting equation constrains a candidate exactly on that image and
leaves at least one codomain value outside it. -/
theorem effective_image_uniqueness
    {X Y Concept Future : Type*}
    (concept : X -> Concept) (future : Y -> Future) (process : X -> Y)
    (descended₁ descended₂ : Concept -> Future)
    (h₁ : future ∘ process = descended₁ ∘ concept)
    (h₂ : future ∘ process = descended₂ ∘ concept) :
    (Function.Surjective concept -> descended₁ = descended₂) ∧
      (¬ Function.Surjective concept ->
        Set.EqOn descended₁ descended₂ (Set.range concept) ∧
          (∀ candidate : Concept -> Future,
            future ∘ process = candidate ∘ concept ↔
              Set.EqOn candidate descended₁ (Set.range concept)) ∧
          ∃ value, value ∉ Set.range concept) := by
  constructor
  · intro hSurjective
    apply hSurjective.injective_comp_right
    exact h₁.symm.trans h₂
  · intro hNotSurjective
    refine ⟨Set.eqOn_range.mpr (h₁.symm.trans h₂), ?_, ?_⟩
    · intro candidate
      constructor
      · intro hCandidate
        apply Set.eqOn_range.mpr
        exact hCandidate.symm.trans h₁
      · intro hOnRange
        exact h₁.trans (Set.eqOn_range.mp hOnRange).symm
    · by_contra hNoOutsideValue
      apply hNotSurjective
      intro value
      by_contra hMissing
      apply hNoOutsideValue
      exact ⟨value, hMissing⟩

/-- A constant readout from `Unit` misses `true`; two descended Boolean maps
can therefore make the same square commute while differing at that value. -/
example :
    let concept : Unit -> Bool := fun _ => false
    let future : Unit -> Bool := fun _ => false
    let process : Unit -> Unit := id
    let descended₁ : Bool -> Bool := id
    let descended₂ : Bool -> Bool := fun _ => false
    future ∘ process = descended₁ ∘ concept ∧
      future ∘ process = descended₂ ∘ concept ∧
        ¬ Function.Surjective concept ∧ descended₁ ≠ descended₂ := by
  dsimp
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro hSurjective
    obtain ⟨state, hstate⟩ := hSurjective true
    exact Bool.noConfusion hstate
  · intro hEqual
    exact Bool.noConfusion (congrFun hEqual true)

#print axioms effective_image_uniqueness

end D5.S0.Rewriting.Quotients.EffectiveImageUniqueness
