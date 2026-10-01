/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog
import Reg.ContractPrototype.Templates.Cut
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

namespace Reg.ContractPrototype.Inline
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

noncomputable section

theorem bridge : LegacyPrimitiveRealization bitArena
    (Boundary (fun b : Bool => b))
    (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)) := ⟨Iff.rfl⟩

def declaration : Registration bounded_run_union_boundary
    PrimitiveLawArena PrimitiveLawArena
    (PrimitiveRealization bitArena.signature)
    (LeanInformationAudit.FiniteLawVariation bitArena)
    (LeanInformationAudit.FiniteSlotSensitivity bitArena) Type Unit Unit where
  targetName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary
  arena := ⟨`D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, bitArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, bitArena⟩
  catalog := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena
  localNames := true
  realization := .legacy bitArena (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)) (((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))).toPrimitiveBundle) ⟨`Reg.ContractPrototype.Inline.bridge, bridge⟩
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))
  variation := some ⟨`D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bitVariation, bitVariation⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bitSensitivity, bitSensitivity⟩
  escapeFrom := some Bool
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := {}

def expectation : ExpectedOccurrence where
  statement := _
  proof := bounded_run_union_boundary
  theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary
  objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena
  statementIdentity := some "sha256:f688347ef95d3a1cf53c6f55feb29b319696b0379f090aaf028b0b756d7a0c03"
  registrationModuleName := `Reg.ContractPrototype.Inline

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.Inline
    expected := #[expectation]
    source := #[expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.Inline }

end
end Reg.ContractPrototype.Inline
