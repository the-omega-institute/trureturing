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

def capturedReadout
    (w : (Bool → Bool) × (Unit → Unit → Bool)) : Bool :=
  decide (w.1 (w.2 () ()) = w.2 () ())

def capturedArena := existentialWitnessArena
  (Arena.ofFintype ((Bool → Bool) × (Unit → Unit → Bool)))
def capturedRealization :=
  @existentialWitnessRealization
    ((Bool → Bool) × (Unit → Unit → Bool))
    (fun w => capturedReadout w = true)
    (fun w => instDecidableEqBool (capturedReadout w) true)
theorem captured_bridge : LegacyPrimitiveRealization capturedArena
    (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g)
    capturedRealization := by
  refine ⟨Iff.trans ?_ (existentialWitnessLegacy _ _).equivalence⟩
  change (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g) ↔
    ∃ w : (Bool → Bool) × (Unit → Unit → Bool), capturedReadout w = true
  constructor
  · rintro ⟨f, g, h⟩
    refine ⟨(f, g), ?_⟩
    have hEq : f (g () ()) = g () () := by
      by_contra hne
      apply h
      intro hmem
      rcases hmem with ⟨u, hu⟩
      cases u
      apply hne
      simpa [diagonal] using congrFun hu.symm ()
    simp [capturedReadout, hEq]
  · rintro ⟨⟨f, g⟩, h⟩
    refine ⟨f, g, ?_⟩
    have hEq : f (g () ()) = g () () := by
      simpa [capturedReadout] using h
    intro hEscaped
    apply hEscaped
    refine ⟨(), ?_⟩
    funext u
    cases u
    simpa [diagonal] using hEq.symm
theorem captured_lawSensitive : capturedArena.Law capturedRealization ∧
    ¬ capturedArena.Law (existentialWitnessRealization (fun _ => False)) := by
  exact ⟨captured_bridge.equivalence.mp exists_captured_listing_of_fixedPoint,
    fun ⟨_, h⟩ => Bool.false_ne_true h⟩
theorem captured_slotSensitive : FiniteSlotSensitivity capturedArena :=
  existentialWitness_sensitivity _ (id, fun _ _ => true)
register_information_theorem exists_captured_listing_of_fixedPoint in capturedArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true))
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
open D5.S3.ConceptDynamics.ConceptJoinUniversal

def recognitionReadout
    (w : (Bool → Bool) × (Bool → Bool) × Bool × Bool) : Bool :=
  (fun a b c d e f : Bool =>
    (fun x : Bool => Bool.casesOn a x (Bool.casesOn b x Bool.false))
      (Bool.casesOn c
        (Bool.casesOn e Bool.false (Bool.casesOn f Bool.false Bool.true))
        (Bool.casesOn d
          (Bool.casesOn e Bool.false (Bool.casesOn f Bool.false Bool.true))
          Bool.true)))
    (decide (w.1 false = w.2.1 false))
    (decide (w.1 true = w.2.1 true))
    (decide (w.1 false = w.2.2.1))
    (decide (w.2.1 false = w.2.2.2))
    (decide (w.1 true = w.2.2.1))
    (decide (w.2.1 true = w.2.2.2))

def recognitionArena := existentialWitnessArena
  (Arena.ofFintype ((Bool → Bool) × (Bool → Bool) × Bool × Bool))
def recognitionRealization :=
  @existentialWitnessRealization
    ((Bool → Bool) × (Bool → Bool) × Bool × Bool)
    (fun w => recognitionReadout w = true)
    (fun w => instDecidableEqBool (recognitionReadout w) true)
theorem recognition_bridge : LegacyPrimitiveRealization recognitionArena
    (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂))
    recognitionRealization := by
  refine ⟨Iff.trans ?_ (existentialWitnessLegacy _ _).equivalence⟩
  change (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
    C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) ↔
    ∃ w : (Bool → Bool) × (Bool → Bool) × Bool × Bool,
      recognitionReadout w = true
  have pointwise (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool) :
      (C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) ↔
        recognitionReadout (C₁, C₂, b₁, b₂) = true := by
    have function_eq_iff (f g : Bool → Bool) :
        f = g ↔ f false = g false ∧ f true = g true := by
      constructor
      · intro h
        exact ⟨congrFun h false, congrFun h true⟩
      · rintro ⟨hFalse, hTrue⟩
        funext b
        cases b
        · exact hFalse
        · exact hTrue
    have hC₁ : C₁ = fun b => Bool.rec (C₁ false) (C₁ true) b := by
      funext b
      cases b <;> rfl
    have hC₂ : C₂ = fun b => Bool.rec (C₂ false) (C₂ true) b := by
      funext b
      cases b <;> rfl
    have hReadout :
        recognitionReadout (C₁, C₂, b₁, b₂) =
          (((! decide (C₁ false = C₂ false)) ||
              (! decide (C₁ true = C₂ true))) &&
            ((decide (C₁ false = b₁) && decide (C₂ false = b₂)) ||
              (decide (C₁ true = b₁) && decide (C₂ true = b₂)))) := by
      unfold recognitionReadout
      cases h₁f : decide (C₁ false = C₂ false) <;>
        cases h₁t : decide (C₁ true = C₂ true) <;>
        cases h₂f : decide (C₁ false = b₁) <;>
        cases h₂t : decide (C₂ false = b₂) <;>
        cases h₃f : decide (C₁ true = b₁) <;>
        cases h₃t : decide (C₂ true = b₂) <;>
        rfl
    rw [hReadout]
    rw [hC₁, hC₂]
    cases h₁f : C₁ false <;> cases h₁t : C₁ true <;>
      cases h₂f : C₂ false <;> cases h₂t : C₂ true <;>
      cases b₁ <;> cases b₂ <;>
      simp [MutuallyRecognized, conceptJoin, function_eq_iff,
        h₁f, h₁t, h₂f, h₂t]
  simp only [Prod.exists]
  simp_rw [pointwise]
theorem recognition_lawSensitive : recognitionArena.Law recognitionRealization ∧
    ¬ recognitionArena.Law (existentialWitnessRealization (fun _ => False)) := by
  exact ⟨recognition_bridge.equivalence.mp mutual_recognition_does_not_require_equal_concepts,
    fun ⟨_, h⟩ => Bool.false_ne_true h⟩
theorem recognition_slotSensitive : FiniteSlotSensitivity recognitionArena :=
  existentialWitness_sensitivity _ (id, id, false, false)
register_information_theorem mutual_recognition_does_not_require_equal_concepts in recognitionArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true))
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

/-- Trigger probe: a new public theorem with no information registration. -/
theorem probe_four_slot_true : ∀ x : Bool, x = x := fun _ => rfl

end D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
