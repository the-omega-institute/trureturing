/- GID: D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mutual recognition is joint realization in one admissible world. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'mutually_recognized_iff_joint_witness' D5 Golden/Frozen/accepted`
     found no repository declaration or accepted duplicate.
   * Searches for mutual recognition, joint realizability, and a `conceptJoin` image
     characterization found no matching theorem or witness in `ConceptDynamics`.
   * `Transport.AdmissionValidityPreservation` uses `Set.MapsTo` for admission-preserving
     transport, not membership in the admitted image of a joint readout.
   * Pinned Mathlib contains `Prod.ext_iff` and basic set-image machinery, but no theorem
     packaging this characterization or either strictness witness. The proofs below use
     only `conceptJoin`, product equality, existential witnesses, and Boolean distinction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability

open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A state pair is mutually recognized when one admissible world realizes its joint
readout. -/
def MutuallyRecognized {World B₁ B₂ : Type _} (Adm : Set World)
    (C₁ : World → B₁) (C₂ : World → B₂) (state : B₁ × B₂) : Prop :=
  ∃ w ∈ Adm, conceptJoin C₁ C₂ w = state

/-- Mutual recognition is exactly simultaneous realization by one admissible world. -/
theorem mutually_recognized_iff_joint_witness
    {World B₁ B₂ : Type _} (Adm : Set World)
    (C₁ : World → B₁) (C₂ : World → B₂) (b₁ : B₁) (b₂ : B₂) :
    MutuallyRecognized Adm C₁ C₂ (b₁, b₂) ↔
      ∃ w, w ∈ Adm ∧ C₁ w = b₁ ∧ C₂ w = b₂ := by
  constructor
  · rintro ⟨w, admissible, jointlyRealizes⟩
    refine ⟨w, admissible, ?_, ?_⟩
    · simpa [conceptJoin] using congrArg Prod.fst jointlyRealizes
    · simpa [conceptJoin] using congrArg Prod.snd jointlyRealizes
  · rintro ⟨w, admissible, realizes₁, realizes₂⟩
    refine ⟨w, admissible, ?_⟩
    apply Prod.ext
    · exact realizes₁
    · exact realizes₂

/-- Mutual recognition can hold even when the two concepts are unequal as functions. -/
theorem mutual_recognition_does_not_require_equal_concepts :
    ∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂) := by
  refine ⟨fun _ ↦ false, id, false, true, ?_, ?_⟩
  · intro equalConcepts
    exact Bool.false_ne_true (congrFun equalConcepts true)
  · exact ⟨true, True.intro, rfl⟩

/-- Separate realization of both descriptions need not give one joint realization. -/
theorem separate_realizability_does_not_imply_mutual_recognition :
    ∃ (Adm : Set Bool) (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      (∃ w ∈ Adm, C₁ w = b₁) ∧
        (∃ w ∈ Adm, C₂ w = b₂) ∧
        ¬MutuallyRecognized Adm C₁ C₂ (b₁, b₂) := by
  refine ⟨Set.univ, id, id, false, true, ?_, ?_, ?_⟩
  · exact ⟨false, True.intro, rfl⟩
  · exact ⟨true, True.intro, rfl⟩
  · rintro ⟨w, _, jointlyRealizes⟩
    have realizesFalse : w = false := by
      simpa [conceptJoin] using congrArg Prod.fst jointlyRealizes
    have realizesTrue : w = true := by
      simpa [conceptJoin] using congrArg Prod.snd jointlyRealizes
    exact Bool.false_ne_true (realizesFalse.symm.trans realizesTrue)

example :
    MutuallyRecognized Set.univ (id : Bool → Bool) (fun b ↦ !b) (false, true) := by
  exact ⟨false, True.intro, rfl⟩

#print axioms mutually_recognized_iff_joint_witness

end D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
