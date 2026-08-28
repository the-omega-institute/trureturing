/- GID: D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a monotone finite support property, inclusion minimality is equivalent to failure after every single deletion. -/

import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.MinimalDependencySupport

/-- A property of finite supports is monotone when adding coordinates preserves it. -/
def MonotoneSupport {Coordinate : Type*}
    (property : Finset Coordinate → Prop) : Prop :=
  ∀ ⦃smaller larger : Finset Coordinate⦄,
    smaller ⊆ larger → property smaller → property larger

/-- A support is inclusion-minimal among supports satisfying a property. -/
def InclusionMinimalSupport {Coordinate : Type*}
    (property : Finset Coordinate → Prop) (support : Finset Coordinate) : Prop :=
  property support ∧
    ∀ ⦃smaller : Finset Coordinate⦄,
      smaller ⊂ support → ¬ property smaller

/-- A support is deletion-minimal when removing any selected coordinate destroys the property. -/
def DeletionMinimalSupport {Coordinate : Type*} [DecidableEq Coordinate]
    (property : Finset Coordinate → Prop) (support : Finset Coordinate) : Prop :=
  property support ∧
    ∀ coordinate ∈ support, ¬ property (support.erase coordinate)

/-- Inclusion minimality always implies deletion minimality. -/
theorem inclusionMinimal_implies_deletionMinimal
    {Coordinate : Type*} [DecidableEq Coordinate]
    {property : Finset Coordinate → Prop} {support : Finset Coordinate}
    (minimal : InclusionMinimalSupport property support) :
    DeletionMinimalSupport property support := by
  refine ⟨minimal.1, ?_⟩
  intro coordinate coordinateIn
  apply minimal.2
  exact Finset.erase_ssubset coordinateIn

/-- Under monotonicity, deletion minimality implies full inclusion minimality. -/
theorem deletionMinimal_implies_inclusionMinimal
    {Coordinate : Type*} [DecidableEq Coordinate]
    {property : Finset Coordinate → Prop} {support : Finset Coordinate}
    (monotone : MonotoneSupport property)
    (minimal : DeletionMinimalSupport property support) :
    InclusionMinimalSupport property support := by
  refine ⟨minimal.1, ?_⟩
  intro smaller properSubset smallerHasProperty
  have existsDeleted : ∃ coordinate, coordinate ∈ support ∧ coordinate ∉ smaller :=
    Finset.exists_of_ssubset properSubset
  obtain ⟨coordinate, coordinateInSupport, coordinateNotInSmaller⟩ := existsDeleted
  apply minimal.2 coordinate coordinateInSupport
  apply monotone ?_ smallerHasProperty
  intro member memberInSmaller
  exact Finset.mem_erase.2
    ⟨fun memberEq => coordinateNotInSmaller (memberEq ▸ memberInSmaller),
      properSubset.1 memberInSmaller⟩

/-- For monotone support properties, the two notions of minimality coincide. -/
theorem inclusionMinimal_iff_deletionMinimal
    {Coordinate : Type*} [DecidableEq Coordinate]
    {property : Finset Coordinate → Prop}
    (monotone : MonotoneSupport property) (support : Finset Coordinate) :
    InclusionMinimalSupport property support ↔
      DeletionMinimalSupport property support := by
  constructor
  · exact inclusionMinimal_implies_deletionMinimal
  · exact deletionMinimal_implies_inclusionMinimal monotone

/-- A minimal support has no redundant selected coordinate. -/
theorem every_member_essential
    {Coordinate : Type*} [DecidableEq Coordinate]
    {property : Finset Coordinate → Prop} {support : Finset Coordinate}
    (monotone : MonotoneSupport property)
    (minimal : InclusionMinimalSupport property support)
    {coordinate : Coordinate} (coordinateIn : coordinate ∈ support) :
    ¬ property (support.erase coordinate) :=
  ((inclusionMinimal_iff_deletionMinimal monotone support).1 minimal).2
    coordinate coordinateIn

#print axioms inclusionMinimal_iff_deletionMinimal
#print axioms every_member_essential

end D5.S3.ConceptDynamics.DagCompletion.MinimalDependencySupport
