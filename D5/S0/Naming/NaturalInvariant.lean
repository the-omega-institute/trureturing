/- GID: D5/S0/Naming/NaturalInvariant
   generality: G
   mirror-B: D5/B/S0/Naming/NaturalInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible quantities form sections, realized by the constant integer-one family. -/

import Mathlib.CategoryTheory.Types.Basic

/- Library-search audit trail (2026-09-01):
   * Repository searches for naming interfaces, natural invariants, compatible
     families, refinements, pushforwards, and `Functor.sections` found no theorem
     combining the general categorical compatibility condition with a concrete
     witness. `CompatibleStageFamily` is restricted to preorder-indexed inverse
     systems, while `finite_cofiltered_limit_nonempty` assumes a finite
     cofiltered diagram.
   * Pinned Mathlib exact hit `Functor.sections` defines a family `u` by the
     condition `F.map f (u j) = u j'` for every morphism `f : j ⟶ j'`.
     `Functor.const` maps every morphism to an identity, so it supplies the
     concrete constant-family witness below. The ordered search stopped at these
     exact Mathlib primitives; no third-party search was needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.NaturalInvariant

open CategoryTheory

universe u v w

/-- A cross-naming natural invariant is exactly a family compatible with every
pushforward. This is Mathlib's `Functor.sections` definition, paired with the
constant integer-one family as a concrete, nonzero-valued witness. -/
theorem naming_natural_invariant_iff_and_integer_witness
    {Name : Type u} [Category.{v} Name] :
    (∀ (quantity : CategoryTheory.Functor Name (Type w))
        (trace : ∀ r, quantity.obj r),
      trace ∈ quantity.sections ↔
        ∀ {r₂ r₁ : Name} (f : r₂ ⟶ r₁),
          quantity.map f (trace r₂) = trace r₁) ∧
      ∃ trace : ((Functor.const Name).obj ℤ).sections,
        trace.1 = fun _ => (1 : ℤ) := by
  constructor
  · intro quantity trace
    rfl
  · refine ⟨⟨fun _ => (1 : ℤ), ?_⟩, rfl⟩
    change ∀ {r₂ r₁ : Name} (f : r₂ ⟶ r₁),
      ((Functor.const Name).obj ℤ).map f (1 : ℤ) = (1 : ℤ)
    intros
    rfl

#print axioms naming_natural_invariant_iff_and_integer_witness

end D5.S0.Naming.NaturalInvariant
