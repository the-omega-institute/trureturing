/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog
import Reg.ContractPrototype.Templates.Iff

namespace Reg.ContractPrototype.DualReadout
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates

def declaration : Registration D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff
    PrimitiveLawArena PrimitiveLawArena
    (PrimitiveRealization dualArena.signature)
    (dualArena.Law dualRealization ∧ ¬ dualArena.Law
      (iffRealization (fun _ : D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity dualArena) Unit Unit Unit where
  targetName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, dualArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, dualArena⟩
  catalog := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
  localNames := true
  realization := .legacy dualArena dualRealization (dualRealization.toPrimitiveBundle) ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge, dual_bridge⟩
  readout := some (@iffRealization
    D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention
    (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_lawSensitive, dual_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_slotSensitive, dual_slotSensitive⟩
  escapeFrom := none
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := {}

def expectation : ExpectedOccurrence where
  statement := _
  proof := D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff
  theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
  statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f"
  registrationModuleName := `Reg.ContractPrototype.DualReadout

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.DualReadout
    expected := #[expectation]
    source := #[expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.DualReadout }

end Reg.ContractPrototype.DualReadout
