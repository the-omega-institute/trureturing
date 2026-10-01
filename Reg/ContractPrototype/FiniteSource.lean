/- L0 原型 -/
import Reg.ContractPrototype.SystemFamily
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

namespace Reg.ContractPrototype.FiniteSource
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.SystemUnit

local instance : DecidableEq arena.State := arena.stateDecidableEq

def declaration : Registration engine_census_self_application
    PrimitiveLawArena PrimitiveLawArena
    (DependentFamily.Realization Reg.ContractPrototype.SystemFamily.signature)
    (LeanInformationAudit.FiniteLawVariation arena)
    (LeanInformationAudit.FiniteSlotSensitivity arena) Unit Unit
    (DependentFamily.Registration Reg.ContractPrototype.SystemFamily.arena SystemStatement) where
  targetName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, arena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena, arena⟩
  catalog := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
  localNames := true
  realization := .legacy arena systemRealization (systemRealization.toPrimitiveBundle) ⟨`D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization,
    system_self_application_realization⟩
  readout := some (DependentFamily.realize Reg.ContractPrototype.SystemFamily.signature
    Reg.ContractPrototype.SystemFamily.actual.readout Reg.ContractPrototype.SystemFamily.actual.anchor)
  variation := some ⟨`Reg.ContractPrototype.SystemFamily.finite_variation,
    Reg.ContractPrototype.SystemFamily.finite_variation⟩
  sensitivity := some ⟨`Reg.ContractPrototype.SystemFamily.finite_sensitivity,
    Reg.ContractPrototype.SystemFamily.finite_sensitivity⟩
  escapeFrom := none
  sourceSelection := some Reg.ContractPrototype.SystemFamily.selection
  continuation := .unknown
  familyRecord := some ⟨`Reg.ContractPrototype.SystemFamily.registration,
    Reg.ContractPrototype.SystemFamily.registration⟩
  options := {}

def expectation : ExpectedOccurrence where
  statement := _
  proof := engine_census_self_application
  theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
  statementIdentity := some "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0"
  registrationModuleName := `Reg.ContractPrototype.FiniteSource

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.FiniteSource
    expected := #[expectation]
    source := #[expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.FiniteSource }

end Reg.ContractPrototype.FiniteSource
