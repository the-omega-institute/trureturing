/- GID: D5/S3/Resource/LogicalReversibleExtension
   generality: G
   mirror-B: D5/B/S3/Resource/LogicalReversibleExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every function into an additive group has a reversible work-register extension. -/

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Logic.Equiv.Prod

namespace D5.S3.Resource.LogicalReversibleExtension

/-- Retaining the input and adding the computed value into a work register makes any function
into an additive group reversible. A zero work register records exactly the function value. -/
theorem logical_reversible_extension {X A : Type*} [AddGroup A] (f : X → A) :
    ∃ e : X × A ≃ X × A,
      (∀ x a, e (x, a) = (x, f x + a)) ∧
      ∀ x, e (x, 0) = (x, f x) := by
  refine ⟨(Equiv.refl X).prodShear (fun x => Equiv.addLeft (f x)), ?_, ?_⟩
  · intro x a
    rfl
  · intro x
    simp

/-- A concrete instance witnesses that the theorem's domain and assumptions are inhabited. -/
example :
    ∃ e : Unit × Int ≃ Unit × Int,
      (∀ x a, e (x, a) = (x, (7 : Int) + a)) ∧
      ∀ x, e (x, 0) = (x, (7 : Int)) :=
  logical_reversible_extension (fun _ : Unit => (7 : Int))

end D5.S3.Resource.LogicalReversibleExtension
