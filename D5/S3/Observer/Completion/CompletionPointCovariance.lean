/- GID: D5/S3/Observer/Completion/CompletionPointCovariance
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/CompletionPointCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predicate-preserving parameter equivalences restrict to completion points. -/

/- Library-search audit trail (2026-08-28):
   * Repository searches found the canonical `completionPointSet` in
     `StructuralCompletionSignature`, but no theorem transporting it across parameter equivalences.
   * Pinned Mathlib's `Equiv.subtypeEquiv` is the exact restriction construction and is applied
     directly below; searches for completion covariance found no proposition-identical theorem.
-/

import D5.S3.Observer.Completion.StructuralCompletionSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.CompletionPointCovariance

open StructuralCompletionSignature

universe u v w z

private theorem completion_membership_covariant
    {A : Type u} {A' : Type v} {D : Type w} {D' : Type z}
    (normalization : Set A) (normalization' : Set A')
    (defect : A -> D) (defect' : A' -> D') (zeroD : D) (zeroD' : D')
    (alpha : A ≃ A')
    (normalization_covariant : forall a,
      a ∈ normalization <-> alpha a ∈ normalization')
    (zero_defect_covariant : forall a,
      defect a = zeroD <-> defect' (alpha a) = zeroD') (a : A) :
    a ∈ completionPointSet normalization defect zeroD <->
      alpha a ∈ completionPointSet normalization' defect' zeroD' := by
  simpa only [completionPointSet, Set.mem_setOf_eq] using
    and_congr (normalization_covariant a) (zero_defect_covariant a)

/-- A parameter equivalence preserving both defining predicates restricts canonically to an
equivalence of completion-point carriers. -/
theorem completion_point_covariance
    {A : Type u} {A' : Type v} {D : Type w} {D' : Type z}
    (normalization : Set A) (normalization' : Set A')
    (defect : A -> D) (defect' : A' -> D') (zeroD : D) (zeroD' : D')
    (alpha : A ≃ A')
    (normalization_covariant : forall a,
      a ∈ normalization <-> alpha a ∈ normalization')
    (zero_defect_covariant : forall a,
      defect a = zeroD <-> defect' (alpha a) = zeroD') :
    Function.Bijective (alpha.subtypeEquiv
      (completion_membership_covariant normalization normalization' defect defect'
        zeroD zeroD' alpha normalization_covariant zero_defect_covariant)) :=
  (alpha.subtypeEquiv
    (completion_membership_covariant normalization normalization' defect defect'
      zeroD zeroD' alpha normalization_covariant zero_defect_covariant)).bijective

#print axioms completion_point_covariance

end D5.S3.Observer.Completion.CompletionPointCovariance
