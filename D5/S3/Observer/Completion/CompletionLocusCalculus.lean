/- GID: D5/S3/Observer/Completion/CompletionLocusCalculus
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/CompletionLocusCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Structural completion loci compose by intersection, pull back along
     arbitrary parameter maps, and retain gauge stability under conjunction. -/

import D5.S3.Observer.Completion.StructuralCompletionSignature

/- Library-search audit trail (2026-08-29):
   * The canonical zero-defect carrier is `completionPointSet` from the existing
     structural completion owner.
   * Pinned Mathlib supplies set intersection and preimage.
   * The results are deliberately set-theoretic; no behavior-reflector claim is
     inferred from a parameter-space zero locus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.CompletionLocusCalculus

open D5.S3.Observer.Completion.StructuralCompletionSignature

universe u v w x y

/-- Conjoining two normalizations and pairing their defects gives exactly the
intersection of their completion loci. -/
theorem completion_locus_pair_eq_inter
    {A : Type u} {D₁ : Type v} {D₂ : Type w}
    (normalization₁ normalization₂ : Set A)
    (defect₁ : A -> D₁) (defect₂ : A -> D₂)
    (zero₁ : D₁) (zero₂ : D₂) :
    completionPointSet (normalization₁ ∩ normalization₂)
        (fun a => (defect₁ a, defect₂ a)) (zero₁, zero₂) =
      completionPointSet normalization₁ defect₁ zero₁ ∩
        completionPointSet normalization₂ defect₂ zero₂ := by
  ext a
  simp [completionPointSet, and_assoc, and_left_comm, and_comm]

/-- Completion loci pull back exactly along arbitrary parameter maps. -/
theorem completion_locus_preimage
    {A : Type u} {A' : Type x} {D : Type y}
    (parameterMap : A' -> A) (normalization : Set A)
    (defect : A -> D) (zeroD : D) :
    completionPointSet (parameterMap ⁻¹' normalization)
        (defect ∘ parameterMap) zeroD =
      parameterMap ⁻¹' completionPointSet normalization defect zeroD := by
  ext a
  rfl

/-- If two completion loci are stable under the same gauge action, their
conjoined locus is stable as well. -/
theorem completion_locus_intersection_gauge_stable
    {G : Type x} {A : Type u} {D₁ : Type v} {D₂ : Type w}
    [Group G] [MulAction G A]
    (normalization₁ normalization₂ : Set A)
    (defect₁ : A -> D₁) (defect₂ : A -> D₂)
    (zero₁ : D₁) (zero₂ : D₂)
    (stable₁ : forall (g : G) {a : A},
      a ∈ completionPointSet normalization₁ defect₁ zero₁ ->
        g • a ∈ completionPointSet normalization₁ defect₁ zero₁)
    (stable₂ : forall (g : G) {a : A},
      a ∈ completionPointSet normalization₂ defect₂ zero₂ ->
        g • a ∈ completionPointSet normalization₂ defect₂ zero₂) :
    forall (g : G) {a : A},
      a ∈ completionPointSet (normalization₁ ∩ normalization₂)
          (fun value => (defect₁ value, defect₂ value)) (zero₁, zero₂) ->
        g • a ∈ completionPointSet (normalization₁ ∩ normalization₂)
          (fun value => (defect₁ value, defect₂ value)) (zero₁, zero₂) := by
  intro g a completion
  have completionInter :
      a ∈ completionPointSet normalization₁ defect₁ zero₁ ∩
        completionPointSet normalization₂ defect₂ zero₂ := by
    simpa only [completion_locus_pair_eq_inter] using completion
  have transportedInter :
      g • a ∈ completionPointSet normalization₁ defect₁ zero₁ ∩
        completionPointSet normalization₂ defect₂ zero₂ :=
    ⟨stable₁ g completionInter.1, stable₂ g completionInter.2⟩
  simpa only [completion_locus_pair_eq_inter] using transportedInter

/-- Pullback along the identity map leaves a completion locus unchanged. -/
example {A : Type u} {D : Type v}
    (normalization : Set A) (defect : A -> D) (zeroD : D) :
    completionPointSet (id ⁻¹' normalization) (defect ∘ id) zeroD =
      completionPointSet normalization defect zeroD := by
  rfl

#print axioms completion_locus_pair_eq_inter
#print axioms completion_locus_preimage
#print axioms completion_locus_intersection_gauge_stable

end D5.S3.Observer.Completion.CompletionLocusCalculus
