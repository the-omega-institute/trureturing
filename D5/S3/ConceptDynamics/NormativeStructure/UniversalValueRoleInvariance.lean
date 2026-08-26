/- GID: D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Structural value schemas survive role relabeling; named privilege does not. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Basic

/- Library-search audit trail (2026-08-26):
   * The semantic search covered D5, Blueprint, Library, Problems, theory,
     Evidence, and Meta/Digestion. The broad value/invariance vocabulary
     matched 1,988 formal or narrative files, 13 theory files, no Evidence
     files, and 196 digestion files; Chronicle is absent from this checkout.
   * `DescriptiveNormativeSeparation` proves that descriptive structure does
     not determine one norm. `SymmetricResponsibilityAllocation` derives a
     uniform allocation at a symmetric event. `TruthfulnessSufficiencyIndependence`
     and `MutualRecognitionIsJointRealizability` separate adjacent communication
     concepts. None states role-natural value schemas or the named-anchor boundary.
   * Pinned Mathlib supplies `Equiv.Perm`, `Equiv.swap`, and Boolean separation.
     `Equiv.Perm.closure_isSwap` is an adjacent finite-generation theorem, but
     the result below is stronger at the schema level: it transports across an
     arbitrary equivalence of role carriers, so no finite-role assumption is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.UniversalValueRoleInvariance

universe u

/-- A role-indexed normative profile keeps permission, harm, and truthful
treatment as separate relations. -/
structure InteractionNorm (Agent : Type u) where
  permitted : Agent -> Agent -> Prop
  harmful : Agent -> Agent -> Prop
  truthful : Agent -> Agent -> Prop

/-- Transport every relation together along a change of role labels. -/
def relabel {Agent Other : Type u} (equivalence : Agent ≃ Other)
    (norm : InteractionNorm Agent) : InteractionNorm Other where
  permitted actor recipient :=
    norm.permitted (equivalence.symm actor) (equivalence.symm recipient)
  harmful actor recipient :=
    norm.harmful (equivalence.symm actor) (equivalence.symm recipient)
  truthful actor recipient :=
    norm.truthful (equivalence.symm actor) (equivalence.symm recipient)

/-- Equal standing excludes identity-sensitive permission differences: a
joint relabeling of actor and recipient cannot change permission. -/
def EqualStanding {Agent : Type u} (norm : InteractionNorm Agent) : Prop :=
  forall (sigma : Equiv.Perm Agent) actor recipient,
    norm.permitted (sigma actor) (sigma recipient) ↔
      norm.permitted actor recipient

/-- Reciprocity requires permission to be symmetric between two roles. -/
def Reciprocity {Agent : Type u} (norm : InteractionNorm Agent) : Prop :=
  forall actor recipient,
    norm.permitted actor recipient ↔ norm.permitted recipient actor

/-- Non-harm excludes every harmful interaction from the permitted set. -/
def NonHarm {Agent : Type u} (norm : InteractionNorm Agent) : Prop :=
  forall actor recipient,
    norm.harmful actor recipient -> Not (norm.permitted actor recipient)

/-- Truthful treatment requires every permitted interaction to be truthful. -/
def TruthfulTreatment {Agent : Type u} (norm : InteractionNorm Agent) : Prop :=
  forall actor recipient,
    norm.permitted actor recipient -> norm.truthful actor recipient

/-- A compact structural core: equal standing, reciprocity, non-harm, and
truthful treatment must all hold in the same normative profile. -/
def StructuralUniversalCore {Agent : Type u}
    (norm : InteractionNorm Agent) : Prop :=
  EqualStanding norm ∧ Reciprocity norm ∧ NonHarm norm ∧ TruthfulTreatment norm

/-- A schema is universal on a role carrier when every permutation of role
names preserves whether the schema holds. -/
def IsUniversalSchema {Agent : Type u}
    (schema : InteractionNorm Agent -> Prop) : Prop :=
  forall (sigma : Equiv.Perm Agent) norm,
    schema (relabel sigma norm) ↔ schema norm

/-- Structural value formulas are natural under every equivalence of role
carriers, not only under permutations of one fixed carrier. -/
theorem structural_universal_core_is_role_natural
    {Agent Other : Type u} (equivalence : Agent ≃ Other)
    (norm : InteractionNorm Agent) :
    StructuralUniversalCore (relabel equivalence norm) ↔
      StructuralUniversalCore norm := by
  constructor
  · rintro ⟨equal, reciprocal, nonHarm, truthful⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro sigma actor recipient
      let conjugate : Equiv.Perm Other :=
        equivalence.symm.trans (sigma.trans equivalence)
      simpa [EqualStanding, relabel, conjugate] using
        equal conjugate (equivalence actor) (equivalence recipient)
    · intro actor recipient
      simpa [Reciprocity, relabel] using
        reciprocal (equivalence actor) (equivalence recipient)
    · intro actor recipient harmful permitted
      exact nonHarm (equivalence actor) (equivalence recipient)
        (by simpa [relabel] using harmful)
        (by simpa [relabel] using permitted)
    · intro actor recipient permitted
      simpa [relabel] using
        truthful (equivalence actor) (equivalence recipient)
          (by simpa [relabel] using permitted)
  · rintro ⟨equal, reciprocal, nonHarm, truthful⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro sigma actor recipient
      let conjugate : Equiv.Perm Agent :=
        equivalence.trans (sigma.trans equivalence.symm)
      simpa [EqualStanding, relabel, conjugate] using
        equal conjugate (equivalence.symm actor) (equivalence.symm recipient)
    · intro actor recipient
      simpa [Reciprocity, relabel] using
        reciprocal (equivalence.symm actor) (equivalence.symm recipient)
    · intro actor recipient harmful permitted
      exact nonHarm (equivalence.symm actor) (equivalence.symm recipient)
        (by simpa [relabel] using harmful)
        (by simpa [relabel] using permitted)
    · intro actor recipient permitted
      simpa [relabel] using
        truthful (equivalence.symm actor) (equivalence.symm recipient)
          (by simpa [relabel] using permitted)

/-- Role naturality specializes to universality under every role permutation. -/
theorem structural_universal_core_is_universal {Agent : Type u} :
    IsUniversalSchema (@StructuralUniversalCore Agent) := by
  intro sigma norm
  exact structural_universal_core_is_role_natural sigma norm

/-- A named privilege anchors permission to one untransported role name. -/
def NamedPrivilege {Agent : Type u} (favored : Agent)
    (norm : InteractionNorm Agent) : Prop :=
  forall recipient, norm.permitted favored recipient

/-- On two roles, privilege for one fixed name fails the same universality
test passed by the structural core. -/
theorem named_privilege_is_not_universal :
    Not (IsUniversalSchema (NamedPrivilege false)) := by
  intro universal
  let norm : InteractionNorm Bool :=
    { permitted := fun actor _ => actor = false
      harmful := fun _ _ => False
      truthful := fun _ _ => True }
  have privileged : NamedPrivilege false norm := by
    intro recipient
    rfl
  have transported :=
    (universal (Equiv.swap false true) norm).mpr privileged
  have impossible := transported false
  simp [relabel, norm] at impossible

#print axioms structural_universal_core_is_role_natural
#print axioms structural_universal_core_is_universal
#print axioms named_privilege_is_not_universal

end D5.S3.ConceptDynamics.NormativeStructure.UniversalValueRoleInvariance
