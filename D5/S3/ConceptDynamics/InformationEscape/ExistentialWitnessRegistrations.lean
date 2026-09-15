/- GID: D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.captured_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations.capturedRealization
   digest: Two frozen existential statements share one witness template without theorem-based simplification. -/

import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations

open ExistentialWitnessRegistrationTemplates LeanInformationAudit

section CapturedListing
open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape

local instance (f : Bool → Bool) (g : Unit → Unit → Bool) : Decidable (IsEscaped f g) := by
  unfold IsEscaped
  infer_instance

def capturedArena := existentialWitnessArena
  (Arena.ofFintype ((Bool → Bool) × (Unit → Unit → Bool)))
def capturedRealization := existentialWitnessRealization
  (fun w : (Bool → Bool) × (Unit → Unit → Bool) => ¬ IsEscaped w.1 w.2)
theorem captured_bridge : LegacyPrimitiveRealization capturedArena
    (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g)
    capturedRealization := by
  refine ⟨Iff.trans ?_ (existentialWitnessLegacy _ _).equivalence⟩
  change (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g) ↔
    ∃ w : (Bool → Bool) × (Unit → Unit → Bool), ¬ IsEscaped w.1 w.2
  simp only [Prod.exists]
theorem captured_lawSensitive : capturedArena.Law capturedRealization ∧
    ¬ capturedArena.Law (existentialWitnessRealization (fun _ => False)) := by
  exact ⟨captured_bridge.equivalence.mp exists_captured_listing_of_fixedPoint,
    fun ⟨_, h⟩ => Bool.false_ne_true h⟩
theorem captured_slotSensitive : FiniteSlotSensitivity capturedArena :=
  existentialWitness_sensitivity _ (id, fun _ _ => true)
register_information_theorem exists_captured_listing_of_fixedPoint in capturedArena
  primitives capturedRealization.toPrimitiveBundle realization captured_bridge
  variation captured_lawSensitive sensitivity captured_slotSensitive
example : exists_captured_listing_of_fixedPoint.__information_unit.Statement =
    (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g) := rfl
#print axioms captured_bridge
#print axioms captured_lawSensitive
#print axioms captured_slotSensitive
expect_information_occurrence exists_captured_listing_of_fixedPoint in capturedArena
  from "D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations"
end CapturedListing

section MutualRecognition
open D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability

local instance (C₁ C₂ : Bool → Bool) (state : Bool × Bool) :
    Decidable (MutuallyRecognized Set.univ C₁ C₂ state) := by
  unfold MutuallyRecognized
  infer_instance

def recognitionArena := existentialWitnessArena
  (Arena.ofFintype ((Bool → Bool) × (Bool → Bool) × Bool × Bool))
def recognitionRealization := existentialWitnessRealization
  (fun w : (Bool → Bool) × (Bool → Bool) × Bool × Bool =>
    w.1 ≠ w.2.1 ∧ MutuallyRecognized Set.univ w.1 w.2.1 (w.2.2.1, w.2.2.2))
theorem recognition_bridge : LegacyPrimitiveRealization recognitionArena
    (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂))
    recognitionRealization := by
  refine ⟨Iff.trans ?_ (existentialWitnessLegacy _ _).equivalence⟩
  change (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
    C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) ↔
    ∃ w : (Bool → Bool) × (Bool → Bool) × Bool × Bool,
      w.1 ≠ w.2.1 ∧ MutuallyRecognized Set.univ w.1 w.2.1 (w.2.2.1, w.2.2.2)
  simp only [Prod.exists]
theorem recognition_lawSensitive : recognitionArena.Law recognitionRealization ∧
    ¬ recognitionArena.Law (existentialWitnessRealization (fun _ => False)) := by
  exact ⟨recognition_bridge.equivalence.mp mutual_recognition_does_not_require_equal_concepts,
    fun ⟨_, h⟩ => Bool.false_ne_true h⟩
theorem recognition_slotSensitive : FiniteSlotSensitivity recognitionArena :=
  existentialWitness_sensitivity _ (id, id, false, false)
register_information_theorem mutual_recognition_does_not_require_equal_concepts in recognitionArena
  primitives recognitionRealization.toPrimitiveBundle realization recognition_bridge
  variation recognition_lawSensitive sensitivity recognition_slotSensitive
example : mutual_recognition_does_not_require_equal_concepts.__information_unit.Statement =
    (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) := rfl
#print axioms recognition_bridge
#print axioms recognition_lawSensitive
#print axioms recognition_slotSensitive
expect_information_occurrence mutual_recognition_does_not_require_equal_concepts in recognitionArena
  from "D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations"
end MutualRecognition

/- The 64-state recognition seal exceeds the default reduction-depth limit. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
