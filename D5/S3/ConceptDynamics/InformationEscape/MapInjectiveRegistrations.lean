/- GID: D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.marker_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations.markerRealization
   digest: Three frozen injectivity theorems share one template with exact statements and checked variation and support. -/

import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.History.Coding.EventCodeIntertranslation
import D5.S3.QuantumContext.ProjectionValuationObstruction
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations

open MapInjectiveRegistrationTemplates LeanInformationAudit

section Marker
open D5.S0.History D5.S0.History.Coding.EventCodeIntertranslation

local instance markerFintype : Fintype Marker :=
  ⟨{.E₀, .E₁}, by intro x; cases x <;> simp⟩

def markerArena := mapInjectiveArena (Arena.ofFintype Marker) Nat
def markerRealization := mapInjectiveRealization markerDigit
theorem marker_bridge : LegacyPrimitiveRealization markerArena
    (Function.Injective markerDigit) markerRealization := mapInjectiveLegacy _ _
theorem marker_lawSensitive : markerArena.Law markerRealization ∧
    ¬ markerArena.Law (mapInjectiveRealization (fun _ => markerDigit .E₀)) := by
  exact ⟨marker_bridge.equivalence.mp marker_digit_injective,
    fun h => (by decide : Marker.E₀ ≠ Marker.E₁) (h rfl)⟩
theorem marker_slotSensitive : FiniteSlotSensitivity markerArena :=
  mapInjective_sensitivity _ markerDigit marker_digit_injective .E₀ .E₁
    (by decide : Marker.E₀ ≠ Marker.E₁)
register_information_theorem marker_digit_injective in markerArena
  primitives markerRealization.toPrimitiveBundle realization marker_bridge
  variation marker_lawSensitive sensitivity marker_slotSensitive
example : marker_digit_injective.__information_unit.Statement =
    Function.Injective markerDigit := rfl
#print axioms marker_bridge
#print axioms marker_lawSensitive
#print axioms marker_slotSensitive
expect_information_occurrence marker_digit_injective in markerArena
  from "D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations"
end Marker

section Opcode
open D5.S0.History D5.S0.History.Coding.EventCodeIntertranslation

local instance opcodeFintype : Fintype Opcode :=
  ⟨{.gen, .enc, .norm, .decode, .length, .phase,
    .read, .ledger, .renorm, .complete, .reflect, .certify}, by intro x; cases x <;> simp⟩

def opcodeArena := mapInjectiveArena (Arena.ofFintype Opcode) Nat
def opcodeRealization := mapInjectiveRealization opcodeIndex
theorem opcode_bridge : LegacyPrimitiveRealization opcodeArena
    (Function.Injective opcodeIndex) opcodeRealization := mapInjectiveLegacy _ _
theorem opcode_lawSensitive : opcodeArena.Law opcodeRealization ∧
    ¬ opcodeArena.Law (mapInjectiveRealization (fun _ => opcodeIndex .gen)) := by
  exact ⟨opcode_bridge.equivalence.mp opcode_index_injective,
    fun h => (by decide : Opcode.gen ≠ Opcode.enc) (h rfl)⟩
theorem opcode_slotSensitive : FiniteSlotSensitivity opcodeArena :=
  mapInjective_sensitivity _ opcodeIndex opcode_index_injective .gen .enc
    (by decide : Opcode.gen ≠ Opcode.enc)
register_information_theorem opcode_index_injective in opcodeArena
  primitives opcodeRealization.toPrimitiveBundle realization opcode_bridge
  variation opcode_lawSensitive sensitivity opcode_slotSensitive
example : opcode_index_injective.__information_unit.Statement =
    Function.Injective opcodeIndex := rfl
#print axioms opcode_bridge
#print axioms opcode_lawSensitive
#print axioms opcode_slotSensitive
expect_information_occurrence opcode_index_injective in opcodeArena
  from "D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations"
end Opcode

section Rays
open D5.S3.QuantumContext.ProjectionValuationObstruction

def rayArena := mapInjectiveArena (Arena.ofFintype (Fin 18)) KSVector
def rayRealization := mapInjectiveRealization ksVectors
theorem ray_bridge : LegacyPrimitiveRealization rayArena
    (Function.Injective ksVectors) rayRealization := mapInjectiveLegacy _ _
theorem ray_lawSensitive : rayArena.Law rayRealization ∧
    ¬ rayArena.Law (mapInjectiveRealization (fun _ => ksVectors 0)) := by
  exact ⟨ray_bridge.equivalence.mp ks_vectors_injective,
    fun h => (by decide : (0 : Fin 18) ≠ 1) (h rfl)⟩
theorem ray_slotSensitive : FiniteSlotSensitivity rayArena :=
  mapInjective_sensitivity _ ksVectors ks_vectors_injective (0 : Fin 18) (1 : Fin 18)
    (by decide : (0 : Fin 18) ≠ 1)
register_information_theorem ks_vectors_injective in rayArena
  primitives rayRealization.toPrimitiveBundle realization ray_bridge
  variation ray_lawSensitive sensitivity ray_slotSensitive
example : ks_vectors_injective.__information_unit.Statement =
    Function.Injective ksVectors := rfl
#print axioms ray_bridge
#print axioms ray_lawSensitive
#print axioms ray_slotSensitive
expect_information_occurrence ks_vectors_injective in rayArena
  from "D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations"
end Rays

set_option maxRecDepth 100000 in
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

end D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
