/- GID: D5/S3/ConceptDynamics/Negation/RelativeComplement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Negation/RelativeComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relative complement is universe-indexed; pullbacks preserve it, images may fail. -/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Bool.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Negation.RelativeComplement

universe u v

/-- Complement of `subset` relative to a chosen ambient region `ambient`. -/
def relativeComplement {X : Type u}
    (ambient subset : Set X) : Set X :=
  ambient \ subset

/-- Enlarging the universe splits relative negation into the old negative region
and the newly admitted region. -/
theorem relativeComplement_domain_extension
    {X : Type u} {A U V : Set X}
    (hAU : A ⊆ U) (hUV : U ⊆ V) :
    relativeComplement V A =
      relativeComplement U A ∪ relativeComplement V U := by
  ext x
  constructor
  · rintro ⟨xInV, xNotInA⟩
    by_cases xInU : x ∈ U
    · exact Or.inl ⟨xInU, xNotInA⟩
    · exact Or.inr ⟨xInV, xInU⟩
  · rintro (xInOld | xInNew)
    · exact ⟨hUV xInOld.1, xInOld.2⟩
    · exact ⟨xInNew.1, fun xInA => xInNew.2 (hAU xInA)⟩

/-- The two pieces in the universe-extension decomposition are disjoint. -/
theorem relativeComplement_domain_extension_disjoint
    {X : Type u} {A U V : Set X} :
    Disjoint (relativeComplement U A) (relativeComplement V U) := by
  refine Set.disjoint_left.2 ?_
  intro x xInOld xInNew
  exact xInNew.2 xInOld.1

/-- Pullback preserves relative complement exactly. -/
theorem preimage_relativeComplement
    {X : Type u} {Y : Type v} (q : X → Y) (U A : Set Y) :
    q ⁻¹' relativeComplement U A =
      relativeComplement (q ⁻¹' U) (q ⁻¹' A) := by
  rfl

/-- Pullback preserves absolute complement exactly. -/
theorem preimage_complement
    {X : Type u} {Y : Type v} (q : X → Y) (A : Set Y) :
    q ⁻¹' Aᶜ = (q ⁻¹' A)ᶜ := by
  rfl

/-- Pullback preserves intersections. -/
theorem preimage_intersection
    {X : Type u} {Y : Type v} (q : X → Y) (A B : Set Y) :
    q ⁻¹' (A ∩ B) = q ⁻¹' A ∩ q ⁻¹' B := by
  rfl

/-- Pullback preserves unions. -/
theorem preimage_union
    {X : Type u} {Y : Type v} (q : X → Y) (A B : Set Y) :
    q ⁻¹' (A ∪ B) = q ⁻¹' A ∪ q ⁻¹' B := by
  rfl

/-- The semantic fiber of one Boolean value is the complement of the other
fiber, even when the source has arbitrarily many states. -/
def booleanFiber {X : Type u} (q : X → Bool) (value : Bool) : Set X :=
  {x | q x = value}

/-- The false fiber is exactly the complement of the true fiber. -/
theorem falseFiber_eq_compl_trueFiber
    {X : Type u} (q : X → Bool) :
    booleanFiber q false = (booleanFiber q true)ᶜ := by
  ext x
  cases h : q x <;> simp [booleanFiber, h]

/-- Direct image does not in general preserve complement, even for a finite
surjective readout. -/
theorem image_complement_counterexample :
    let q : Bool × Bool → Bool := Prod.fst
    let A : Set (Bool × Bool) := {(false, false)}
    q '' Aᶜ ≠ (q '' A)ᶜ := by
  dsimp
  intro imageEquality
  have falseInImageComplement :
      false ∈
        (Prod.fst : Bool × Bool → Bool) ''
          ({(false, false)} : Set (Bool × Bool))ᶜ := by
    refine ⟨(false, true), ?_, rfl⟩
    simp
  rw [imageEquality] at falseInImageComplement
  exact falseInImageComplement
    ⟨(false, false), by simp, rfl⟩

#print axioms relativeComplement_domain_extension
#print axioms preimage_relativeComplement
#print axioms falseFiber_eq_compl_trueFiber
#print axioms image_complement_counterexample

end D5.S3.ConceptDynamics.Negation.RelativeComplement
