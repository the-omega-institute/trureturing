/- GID: D5/S0/Rewriting/Classification/SubobjectClassifierCoordinate
   generality: G
   mirror-B: D5/B/S0/Rewriting/Classification/SubobjectClassifierCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A subobject classifier bijectively coordinates subobjects by characteristic morphisms. -/

import Mathlib.CategoryTheory.Subobject.Classifier.Defs

/- Library-search audit trail (2026-08-15):
   * Pinned Mathlib defines `Subobject.Classifier.representableBy`, an exact
     equivalence between morphisms into the classifier and subobjects.
   * Pinned Mathlib also proves
     `hasSubobjectClassifier_iff_isRepresentable`; the theorem below uses the
     more precise bundled equivalence instead of reproving representability.
   * Repository searches for `Subobject.Classifier`,
     `HasSubobjectClassifier`, and `representableBy.homEquiv.bijective` found
     no D5 declaration for this classification example.
-/

namespace D5.S0.Rewriting.Classification.SubobjectClassifierCoordinate

open CategoryTheory

universe u v

/-- A subobject classifier turns characteristic morphisms into a lossless
coordinate system for subobjects: pullback of truth is both injective and
surjective. -/
theorem subobject_classifier_coordinate_bijection
    {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
    (classifier : Subobject.Classifier C) (X : C) :
    Function.Bijective
      (fun characteristic : X ⟶ classifier.Ω =>
        (Subobject.pullback characteristic).obj classifier.truth_as_subobject) := by
  exact classifier.representableBy.homEquiv.bijective

end D5.S0.Rewriting.Classification.SubobjectClassifierCoordinate
