/- GID: D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MembershipRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.two_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations.twoRealization
   digest: Two frozen annihilator membership statements retain their predicates and anchors in one finite object catalog. -/

import D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S3.Fourier.FinitePoisson
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations

open MembershipRegistrationTemplates LeanInformationAudit
open D5.S3.Fourier.FinitePoisson

-- Keep the decision folded while elaborating the existing membership witnesses.
@[irreducible] local instance membershipDecidable :
    DecidablePred (fun x : ZMod 4 => x ∈ (annihilator evenSubgroupFour : Set (ZMod 4))) := fun k =>
  letI : DecidablePred (· ∈ evenSubgroupFour) :=
    AddMonoidHom.decidableMemKer
      (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom
  decidable_of_iff (∀ h ∈ evenSubgroupFour, (k * h : ZMod 4) = 0) (by
    change (∀ h ∈ evenSubgroupFour, (k * h : ZMod 4) = 0) ↔
      ∀ h ∈ evenSubgroupFour, character k h = 1
    apply forall_congr'
    intro h
    apply forall_congr'
    intro _
    exact (AddChar.IsPrimitive.zmod_char_eq_one_iff 4
      (ZMod.isPrimitive_stdAddChar 4) (k * h)).symm)

#print axioms membershipDecidable

noncomputable section

def objectArena : Arena := Arena.ofFintype (ZMod 4)
def memberArena := membershipArena objectArena true
def nonmemberArena := membershipArena objectArena false
theorem member_slotSensitive : FiniteSlotSensitivity memberArena :=
  membership_sensitivity _ true (2 : ZMod 4) (1 : ZMod 4) (by change (2 : ZMod 4) ≠ 1; decide)
theorem nonmember_slotSensitive : FiniteSlotSensitivity nonmemberArena :=
  membership_sensitivity _ false (2 : ZMod 4) (1 : ZMod 4) (by change (2 : ZMod 4) ≠ 1; decide)

def twoRealization := @membershipRealization (ZMod 4) (annihilator evenSubgroupFour : Set (ZMod 4))
  membershipDecidable (2 : ZMod 4)
theorem two_bridge : LegacyPrimitiveRealization memberArena
    ((2 : ZMod 4) ∈ annihilator evenSubgroupFour) twoRealization :=
  @membershipLegacy objectArena true _ membershipDecidable (2 : ZMod 4)
theorem two_lawSensitive : memberArena.Law twoRealization ∧
    ¬ memberArena.Law (@membershipRealization (ZMod 4) (annihilator evenSubgroupFour : Set (ZMod 4))
      membershipDecidable (1 : ZMod 4)) :=
  ⟨two_bridge.equivalence.mp two_mem_annihilator_evenSubgroupFour,
    fun h => one_not_mem_annihilator_evenSubgroupFour
      (@of_decide_eq_true ((1 : ZMod 4) ∈ (annihilator evenSubgroupFour : Set (ZMod 4)))
        (membershipDecidable 1) h)⟩
register_information_theorem two_mem_annihilator_evenSubgroupFour in memberArena
  object_arena objectArena catalog annihilatorMembership
  primitives twoRealization.toPrimitiveBundle realization two_bridge
  variation two_lawSensitive sensitivity member_slotSensitive
example : two_mem_annihilator_evenSubgroupFour.«D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations/D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations.objectArena/annihilatorMembership».__information_unit.Statement =
    ((2 : ZMod 4) ∈ annihilator evenSubgroupFour) := rfl
#print axioms two_bridge
#print axioms two_lawSensitive
expect_information_occurrence two_mem_annihilator_evenSubgroupFour in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations"

def oneRealization := @membershipRealization (ZMod 4) (annihilator evenSubgroupFour : Set (ZMod 4))
  membershipDecidable (1 : ZMod 4)
theorem one_bridge : LegacyPrimitiveRealization nonmemberArena
    ((1 : ZMod 4) ∉ annihilator evenSubgroupFour) oneRealization :=
  @membershipLegacy objectArena false _ membershipDecidable (1 : ZMod 4)
theorem one_lawSensitive : nonmemberArena.Law oneRealization ∧
    ¬ nonmemberArena.Law (@membershipRealization (ZMod 4) (annihilator evenSubgroupFour : Set (ZMod 4))
      membershipDecidable (2 : ZMod 4)) :=
  ⟨one_bridge.equivalence.mp one_not_mem_annihilator_evenSubgroupFour,
    fun h => (of_decide_eq_false h) two_mem_annihilator_evenSubgroupFour⟩
register_information_theorem one_not_mem_annihilator_evenSubgroupFour in nonmemberArena
  object_arena objectArena catalog annihilatorMembership
  primitives oneRealization.toPrimitiveBundle realization one_bridge
  variation one_lawSensitive sensitivity nonmember_slotSensitive
example : one_not_mem_annihilator_evenSubgroupFour.«D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations/D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations.objectArena/annihilatorMembership».__information_unit.Statement =
    ((1 : ZMod 4) ∉ annihilator evenSubgroupFour) := rfl
#print axioms one_bridge
#print axioms one_lawSensitive
expect_information_occurrence one_not_mem_annihilator_evenSubgroupFour in objectArena
  from "D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations"

#print axioms member_slotSensitive
#print axioms nonmember_slotSensitive
#print axioms twoRealization
#print axioms oneRealization
/- The original annihilator readout is decided by finite modular multiplication.
No finite seal is asserted here. -/

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],anchor[0]]"
      else
        logWarning diagnostic

end

end D5.S3.ConceptDynamics.InformationEscape.MembershipRegistrations
