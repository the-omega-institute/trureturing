/- GID: D5/S3/Observer/Dynamics/TopologicalFactorMinimality
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous surjective equivariant factors descend forward-orbit minimality. -/

import Mathlib.Dynamics.Minimal

/-! Continuous surjective equivariant factors descend forward-orbit minimality. -/

open Set Function

namespace D5.S3.Observer.Dynamics.TopologicalFactorMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A continuous surjective equivariant map sends a minimal additive action to a
minimal additive action.  No compactness or separation hypotheses are needed. -/
theorem continuous_surjective_equivariant_minimality
    {M X Y : Type*} [AddMonoid M]
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddAction M X] [AddAction M Y]
    [AddAction.IsMinimal M X]
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f)
    (hequiv : ∀ (m : M) (x : X), f (m +ᵥ x) = m +ᵥ f x) :
    AddAction.IsMinimal M Y := by
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  apply dense_iff_closure_eq.2
  apply eq_univ_iff_forall.2
  intro y'
  obtain ⟨x', rfl⟩ := hsurj y'
  apply map_mem_closure hf (AddAction.dense_orbit M x x')
  rintro _ ⟨m, rfl⟩
  exact ⟨m, (hequiv m x).symm⟩

/-- The forward-orbit form of the factor theorem, for a single continuous map.
This is the form used by symbolic subshifts and observation factors. -/
theorem dense_forward_orbit_of_continuous_surjective_semiconj
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (g : Y → Y) (factor : X → Y)
    (hfactor : Continuous factor) (hsurj : Surjective factor)
    (hsemiconj : Semiconj factor f g)
    (hminimal : ∀ x : X, Dense (Set.range fun n : ℕ => (f^[n]) x)) :
    ∀ y : Y, Dense (Set.range fun n : ℕ => (g^[n]) y) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  apply dense_iff_closure_eq.2
  apply eq_univ_iff_forall.2
  intro y'
  obtain ⟨x', rfl⟩ := hsurj y'
  apply map_mem_closure hfactor (hminimal x x')
  rintro _ ⟨n, rfl⟩
  exact ⟨n, (hsemiconj.iterate_right n x).symm⟩

#print axioms continuous_surjective_equivariant_minimality
#print axioms dense_forward_orbit_of_continuous_surjective_semiconj

end D5.S3.Observer.Dynamics.TopologicalFactorMinimality
