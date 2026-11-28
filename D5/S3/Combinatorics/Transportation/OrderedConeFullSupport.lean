/- GID: D5/S3/Combinatorics/Transportation/OrderedConeFullSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/OrderedConeFullSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density characterizes full permitted support over the original ordered-group cone. -/

import D5.S3.Algebra.Refinement.OrderedConeFullSupport

/-! Density is exactly the condition for simultaneous full permitted support.
The reusable construction is in `Omega.Refinement`; the coefficient cone here
is Mathlib's original subtype, with its original additive operations.
-/

namespace D5.S3.Combinatorics.Transportation.OrderedConeFullSupport
open scoped BigOperators
universe u v w z

open Classical in
/-- Every balanced finite-fiber problem has precisely its full permitted support
if and only if the original ordered additive group is densely ordered. -/
theorem density_iff_full_permitted_support
    (G : Type u) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :
    DenselyOrdered G ↔
      (∀ (A : Type v) (B : Type w) (Z : Type z) [Fintype A] [Fintype B]
        (f : A → Z) (g : B → Z) (p : A → Nonneg G) (q : B → Nonneg G),
        (∀ c, (∑ a, if f a = c then p a else 0) =
          ∑ b, if g b = c then q b else 0) →
        ∃ m : A → B → Nonneg G,
          (∀ a b, f a ≠ g b → m a b = 0) ∧
          (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b) ∧
          (∀ a b, m a b ≠ 0 ↔ f a = g b ∧ p a ≠ 0 ∧ q b ≠ 0)) :=
  Omega.Refinement.densely_ordered_iff_full_support_transport

#print axioms density_iff_full_permitted_support
end D5.S3.Combinatorics.Transportation.OrderedConeFullSupport
