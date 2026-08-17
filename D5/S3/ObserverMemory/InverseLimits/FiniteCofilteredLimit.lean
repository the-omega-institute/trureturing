/- GID: D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A cofiltered limit of nonempty finite types is nonempty. -/

import Mathlib.CategoryTheory.CofilteredSystem

/- Library-search audit trail (2026-08-17):
   * Exact pinned-Mathlib and Loogle hit
     `nonempty_sections_of_finite_cofiltered_system` has precisely the
     cofiltered, objectwise finite, objectwise nonempty hypotheses and the
     compatible-section nonemptiness conclusion; it is applied directly.
   * The related repository candidate-section theorem adds invariant subsets
     and does not expose this general compatible-section statement.
   * LeanSearch's shaped query endpoint returned HTTP 404 and no usable hit.
-/

namespace D5.S3.ObserverMemory.InverseLimits.FiniteCofilteredLimit

open CategoryTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

/-- Every cofiltered diagram of nonempty finite types has a compatible
section, hence its inverse limit is nonempty. -/
theorem finite_cofiltered_limit_nonempty {J : Type u} [Category.{w} J]
    [IsCofiltered J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  exact nonempty_sections_of_finite_cofiltered_system F

example : Nonempty Bool := ⟨false⟩

example : ((Functor.const Unit).obj Bool).sections.Nonempty := by
  let F : Unit ⥤ Type := (Functor.const Unit).obj Bool
  letI : ∀ j, Finite (F.obj j) := fun _ => by
    change Finite Bool
    infer_instance
  letI : ∀ j, Nonempty (F.obj j) := fun _ => by
    change Nonempty Bool
    exact ⟨false⟩
  simpa [F] using finite_cofiltered_limit_nonempty F

#print axioms finite_cofiltered_limit_nonempty

end D5.S3.ObserverMemory.InverseLimits.FiniteCofilteredLimit
