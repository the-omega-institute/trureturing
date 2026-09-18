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

/-- The original digits 0 and 1, represented by the two Boolean constructors. -/
def markerReadout (m : Marker) : Bool := Marker.casesOn m false true

def markerArena := mapInjectiveArena (Arena.ofFintype Marker) Bool
def markerRealization :=
  @mapInjectiveRealization Marker Bool instDecidableEqBool (fun m => markerReadout m)
theorem marker_bridge : LegacyPrimitiveRealization markerArena
    (Function.Injective markerDigit) markerRealization := by
  constructor
  change Function.Injective markerDigit ↔ Function.Injective markerReadout
  have same_values (x y : Marker) : markerDigit x = markerDigit y ↔
      markerReadout x = markerReadout y := by
    cases x <;> cases y <;> simp [markerDigit, markerReadout]
  exact ⟨fun h _ _ e => h ((same_values _ _).mpr e),
    fun h _ _ e => h ((same_values _ _).mp e)⟩
theorem marker_lawSensitive : markerArena.Law markerRealization ∧
    ¬ markerArena.Law (mapInjectiveRealization (fun _ => markerReadout .E₀)) := by
  exact ⟨marker_bridge.equivalence.mp marker_digit_injective,
    fun h => (by decide : Marker.E₀ ≠ Marker.E₁) (h rfl)⟩
theorem marker_slotSensitive : FiniteSlotSensitivity markerArena :=
  mapInjective_sensitivity _ (fun m => markerReadout m)
    (marker_bridge.equivalence.mp marker_digit_injective) .E₀ .E₁
    (by decide : Marker.E₀ ≠ Marker.E₁)
register_information_theorem marker_digit_injective in markerArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization D5.S0.History.Marker Bool instDecidableEqBool (fun m => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerReadout m))
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

/-- The four binary digits of the original opcode index, most significant first. -/
def opcodeReadout (o : Opcode) : Bool × Bool × Bool × Bool :=
  Opcode.casesOn o
    (false, false, false, false)
    (false, false, false, true)
    (false, false, true, false)
    (false, false, true, true)
    (false, true, false, false)
    (false, true, false, true)
    (false, true, true, false)
    (false, true, true, true)
    (true, false, false, false)
    (true, false, false, true)
    (true, false, true, false)
    (true, false, true, true)

def opcodeArena := mapInjectiveArena (Arena.ofFintype Opcode) (Bool × Bool × Bool × Bool)
def opcodeRealization :=
  @mapInjectiveRealization Opcode (Bool × Bool × Bool × Bool)
    (inferInstance : DecidableEq (Bool × Bool × Bool × Bool)) (fun o => opcodeReadout o)
theorem opcode_bridge : LegacyPrimitiveRealization opcodeArena
    (Function.Injective opcodeIndex) opcodeRealization := by
  constructor
  change Function.Injective opcodeIndex ↔ Function.Injective opcodeReadout
  have same_values (x y : Opcode) : opcodeIndex x = opcodeIndex y ↔
      opcodeReadout x = opcodeReadout y := by
    cases x <;> cases y <;> simp [opcodeIndex, opcodeReadout]
  exact ⟨fun h _ _ e => h ((same_values _ _).mpr e),
    fun h _ _ e => h ((same_values _ _).mp e)⟩
theorem opcode_lawSensitive : opcodeArena.Law opcodeRealization ∧
    ¬ opcodeArena.Law (mapInjectiveRealization (fun _ => opcodeReadout .gen)) := by
  exact ⟨opcode_bridge.equivalence.mp opcode_index_injective,
    fun h => (by decide : Opcode.gen ≠ Opcode.enc) (h rfl)⟩
theorem opcode_slotSensitive : FiniteSlotSensitivity opcodeArena :=
  mapInjective_sensitivity _ (fun o => opcodeReadout o)
    (opcode_bridge.equivalence.mp opcode_index_injective) .gen .enc
    (by decide : Opcode.gen ≠ Opcode.enc)
register_information_theorem opcode_index_injective in opcodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization D5.S0.History.Opcode (Bool × Bool × Bool × Bool) (inferInstance : DecidableEq (Bool × Bool × Bool × Bool)) (fun o => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeReadout o))
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

/-- A coordinate is 0, -1, or 1, encoded respectively by none, some false, or some true. -/
abbrev RayCode := Option Bool × Option Bool × Option Bool × Option Bool

/-- The eighteen original rows, retaining all four coordinates in a finite carrier. -/
def rayReadout (r : Fin 18) : RayCode :=
  Bool.casesOn (decide (r = (⟨0, (let h : Nat.lt 0 18 := (by change 0 < 18; omega); h)⟩ : Fin 18)))
    (Bool.casesOn (decide (r = (⟨1, (let h : Nat.lt 1 18 := (by change 1 < 18; omega); h)⟩ : Fin 18)))
      (Bool.casesOn (decide (r = (⟨2, (let h : Nat.lt 2 18 := (by change 2 < 18; omega); h)⟩ : Fin 18)))
        (Bool.casesOn (decide (r = (⟨3, (let h : Nat.lt 3 18 := (by change 3 < 18; omega); h)⟩ : Fin 18)))
          (Bool.casesOn (decide (r = (⟨4, (let h : Nat.lt 4 18 := (by change 4 < 18; omega); h)⟩ : Fin 18)))
            (Bool.casesOn (decide (r = (⟨5, (let h : Nat.lt 5 18 := (by change 5 < 18; omega); h)⟩ : Fin 18)))
              (Bool.casesOn (decide (r = (⟨6, (let h : Nat.lt 6 18 := (by change 6 < 18; omega); h)⟩ : Fin 18)))
                (Bool.casesOn (decide (r = (⟨7, (let h : Nat.lt 7 18 := (by change 7 < 18; omega); h)⟩ : Fin 18)))
                  (Bool.casesOn (decide (r = (⟨8, (let h : Nat.lt 8 18 := (by change 8 < 18; omega); h)⟩ : Fin 18)))
                    (Bool.casesOn (decide (r = (⟨9, (let h : Nat.lt 9 18 := (by change 9 < 18; omega); h)⟩ : Fin 18)))
                      (Bool.casesOn (decide (r = (⟨10, (let h : Nat.lt 10 18 := (by change 10 < 18; omega); h)⟩ : Fin 18)))
                        (Bool.casesOn (decide (r = (⟨11, (let h : Nat.lt 11 18 := (by change 11 < 18; omega); h)⟩ : Fin 18)))
                          (Bool.casesOn (decide (r = (⟨12, (let h : Nat.lt 12 18 := (by change 12 < 18; omega); h)⟩ : Fin 18)))
                            (Bool.casesOn (decide (r = (⟨13, (let h : Nat.lt 13 18 := (by change 13 < 18; omega); h)⟩ : Fin 18)))
                              (Bool.casesOn (decide (r = (⟨14, (let h : Nat.lt 14 18 := (by change 14 < 18; omega); h)⟩ : Fin 18)))
                                (Bool.casesOn (decide (r = (⟨15, (let h : Nat.lt 15 18 := (by change 15 < 18; omega); h)⟩ : Fin 18)))
                                  (Bool.casesOn (decide (r = (⟨16, (let h : Nat.lt 16 18 := (by change 16 < 18; omega); h)⟩ : Fin 18)))
                                    ((some true, none, some false, none))
                                    (some true, some false, some true, some false))
                                  (some true, some true, some true, some false))
                                (some true, none, none, some true))
                              (none, some true, none, some true))
                            (none, some true, none, some false))
                          (some true, some true, some true, some true))
                        (some true, some true, some false, some false))
                      (some true, some false, some true, some true))
                    (some true, some false, some false, some false))
                  (none, none, some true, some false))
                (some true, none, none, none))
              (none, some true, some true, none))
            (none, some true, some false, none))
          (some true, some true, none, none))
        (some true, some false, none, none))
      (none, none, some true, none))
    (none, none, none, some true)

def rayArena := mapInjectiveArena (Arena.ofFintype (Fin 18)) RayCode
def rayRealization :=
  @mapInjectiveRealization (Fin 18) RayCode
    (inferInstance : DecidableEq RayCode) (fun r => rayReadout r)
theorem ray_bridge : LegacyPrimitiveRealization rayArena
    (Function.Injective ksVectors) rayRealization := by
  constructor
  change Function.Injective ksVectors ↔ Function.Injective rayReadout
  let encodeDigit (z : Int) : Option Bool := if z = 0 then none else some (decide (z = 1))
  let encode (v : KSVector) : RayCode :=
    (encodeDigit (v 0), encodeDigit (v 1), encodeDigit (v 2), encodeDigit (v 3))
  let decodeDigit : Option Bool → Int
    | none => 0
    | some false => -1
    | some true => 1
  let decode (v : RayCode) : KSVector :=
    ![decodeDigit v.1, decodeDigit v.2.1, decodeDigit v.2.2.1, decodeDigit v.2.2.2]
  have encoded (r : Fin 18) : encode (ksVectors r) = rayReadout r := by
    fin_cases r <;> decide
  have decoded (r : Fin 18) : decode (rayReadout r) = ksVectors r := by
    fin_cases r <;> decide
  have same_values (r s : Fin 18) : ksVectors r = ksVectors s ↔
      rayReadout r = rayReadout s := by
    constructor
    · intro h
      rw [← encoded r, ← encoded s, h]
    · intro h
      rw [← decoded r, ← decoded s, h]
  exact ⟨fun h _ _ e => h ((same_values _ _).mpr e),
    fun h _ _ e => h ((same_values _ _).mp e)⟩
theorem ray_lawSensitive : rayArena.Law rayRealization ∧
    ¬ rayArena.Law (mapInjectiveRealization (fun _ => rayReadout 0)) := by
  exact ⟨ray_bridge.equivalence.mp ks_vectors_injective,
    fun h => (by decide : (0 : Fin 18) ≠ 1) (h rfl)⟩
theorem ray_slotSensitive : FiniteSlotSensitivity rayArena :=
  mapInjective_sensitivity _ (fun r => rayReadout r)
    (ray_bridge.equivalence.mp ks_vectors_injective) (0 : Fin 18) (1 : Fin 18)
    (by decide : (0 : Fin 18) ≠ 1)
register_information_theorem ks_vectors_injective in rayArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (inferInstance : DecidableEq D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r))
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
