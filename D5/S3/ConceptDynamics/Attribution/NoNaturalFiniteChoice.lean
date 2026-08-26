/- GID: D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No selector on every nonempty finite carrier can be invariant under all bijections. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.NoNaturalFiniteChoice

/- A natural family assigns an element to each finite nonempty carrier and transports it
   along every bijection. The two-point carrier makes such invariance impossible. -/
theorem no_natural_finite_choice :
    ¬ ∃ (choice : ∀ (α : Type) (_ : Fintype α) (_ : Nonempty α), α),
      ∀ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
        (hα : Nonempty α) (hβ : Nonempty β) (e : α ≃ β),
          e (choice α fα hα) = choice β fβ hβ := by
  rintro ⟨choice, naturality⟩
  let α := Fin 2
  let fα : Fintype α := inferInstance
  let hα : Nonempty α := inferInstance
  let c : α := choice α fα hα
  let e : α ≃ α := Equiv.swap 0 1
  have hfixed : e c = c := by
    simpa [c] using naturality α α fα fα hα hα e
  rcases Fin.eq_zero_or_eq_succ c with hc | ⟨i, hc⟩
  · simpa [hc, e] using hfixed
  · have hi : i = 0 := Fin.eq_zero i
    simpa [hc, hi, e] using hfixed

#print axioms no_natural_finite_choice

end D5.S3.ConceptDynamics.Attribution.NoNaturalFiniteChoice
