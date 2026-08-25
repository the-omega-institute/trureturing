/- GID: D5/S3/ConceptDynamics/Negation/InvolutiveNegation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Negation/InvolutiveNegation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Point negation selects from complements; involution adds reversible coherence. -/

import D5.S3.ConceptDynamics.Negation.RelativeComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Negation.InvolutiveNegation

universe u

/-- The region of all points different from `x`. -/
def pointComplement {X : Type u} (x : X) : Set X :=
  {y | y ≠ x}

/-- A point-valued selector from every point-complement region. -/
structure AvoidanceSelector (X : Type u) where
  choose : X → X
  avoids : ∀ x, choose x ≠ x

/-- A reversible coherent point-negation: every point is paired with a distinct
partner and applying negation twice returns to the starting point. -/
structure InvolutiveNegation (X : Type u) where
  neg : X → X
  involutive : Function.Involutive neg
  fixedPointFree : ∀ x, neg x ≠ x

/-- Every involutive negation is in particular an avoidance selector. -/
def InvolutiveNegation.toAvoidanceSelector
    {X : Type u} (negation : InvolutiveNegation X) :
    AvoidanceSelector X :=
  ⟨negation.neg, negation.fixedPointFree⟩

/-- Membership in a point-complement is exactly inequality. -/
theorem mem_pointComplement_iff
    {X : Type u} {x y : X} :
    y ∈ pointComplement x ↔ y ≠ x := by
  rfl

/-- The selected value always lies in the corresponding point-complement. -/
theorem avoidanceSelector_mem_pointComplement
    {X : Type u} (selector : AvoidanceSelector X) (x : X) :
    selector.choose x ∈ pointComplement x :=
  selector.avoids x

/-- A function pointwise realizes singleton complement when the complement of
each singleton is itself the singleton selected by the function. -/
def SingletonComplementing
    {X : Type u} (neg : X → X) : Prop :=
  ∀ x, ({neg x} : Set X) = ({x} : Set X)ᶜ

/-- Singleton-complement realization is necessarily fixed-point free. -/
theorem singletonComplementing_fixedPointFree
    {X : Type u} {neg : X → X}
    (complements : SingletonComplementing neg) :
    ∀ x, neg x ≠ x := by
  intro x
  have selectedInComplement : neg x ∈ ({x} : Set X)ᶜ := by
    rw [← complements x]
    simp
  simpa using selectedInComplement

/-- If singleton complements remain singleton-valued, every point is either the
chosen base point or its selected complement. -/
theorem singletonComplementing_exhausts_two_points
    {X : Type u} {neg : X → X}
    (complements : SingletonComplementing neg) (x y : X) :
    y = x ∨ y = neg x := by
  by_cases yEquals : y = x
  · exact Or.inl yEquals
  · right
    have yInComplement : y ∈ ({x} : Set X)ᶜ := by
      simpa using yEquals
    have yInSelected : y ∈ ({neg x} : Set X) := by
      rw [complements x]
      exact yInComplement
    simpa using yInSelected

/-- At any supplied base point, singleton-complement realization exhibits an
exact two-point cover by distinct elements. -/
theorem singletonComplementing_two_point_cover
    {X : Type u} {neg : X → X}
    (complements : SingletonComplementing neg) (x : X) :
    x ≠ neg x ∧ ∀ y, y = x ∨ y = neg x := by
  refine ⟨(singletonComplementing_fixedPointFree complements x).symm, ?_⟩
  intro y
  exact singletonComplementing_exhausts_two_points complements x y

/-- Three pairwise distinct points obstruct singleton-valued point
complementation. -/
theorem no_singletonComplementing_of_three_distinct
    {X : Type u} (a b c : X)
    (aNeB : a ≠ b) (aNeC : a ≠ c) (bNeC : b ≠ c) :
    ¬∃ neg : X → X, SingletonComplementing neg := by
  rintro ⟨neg, complements⟩
  have bCases :=
    singletonComplementing_exhausts_two_points complements a b
  have cCases :=
    singletonComplementing_exhausts_two_points complements a c
  have bEquals : b = neg a :=
    bCases.resolve_left aNeB.symm
  have cEquals : c = neg a :=
    cCases.resolve_left aNeC.symm
  exact bNeC (bEquals.trans cEquals.symm)

/-- Boolean negation is the canonical nontrivial instance in which singleton
complement is again singleton-valued. -/
theorem bool_singletonComplementing :
    SingletonComplementing (fun value : Bool => !value) := by
  intro value
  ext other
  cases value <;> cases other <;> decide

/-- The action induced by an involutive negation on subsets. -/
def imageSet {X : Type u}
    (negation : InvolutiveNegation X) (subset : Set X) : Set X :=
  negation.neg '' subset

/-- Membership in the image subset can be tested by applying the involution. -/
theorem mem_imageSet_iff
    {X : Type u} (negation : InvolutiveNegation X)
    (subset : Set X) (x : X) :
    x ∈ imageSet negation subset ↔ negation.neg x ∈ subset := by
  constructor
  · rintro ⟨y, yInSubset, rfl⟩
    simpa only [negation.involutive y] using yInSubset
  · intro negatedInSubset
    exact ⟨negation.neg x, negatedInSubset, negation.involutive x⟩

/-- The induced subset action is itself involutive. -/
theorem imageSet_involutive
    {X : Type u} (negation : InvolutiveNegation X)
    (subset : Set X) :
    imageSet negation (imageSet negation subset) = subset := by
  ext x
  simp only [mem_imageSet_iff, negation.involutive x]

/-- A bijective involutive negation commutes with Boolean complement on the
powerset. -/
theorem imageSet_complement
    {X : Type u} (negation : InvolutiveNegation X)
    (subset : Set X) :
    imageSet negation subsetᶜ = (imageSet negation subset)ᶜ := by
  ext x
  simp only [mem_imageSet_iff, Set.mem_compl_iff]

#print axioms singletonComplementing_two_point_cover
#print axioms no_singletonComplementing_of_three_distinct
#print axioms bool_singletonComplementing
#print axioms imageSet_involutive
#print axioms imageSet_complement

end D5.S3.ConceptDynamics.Negation.InvolutiveNegation
