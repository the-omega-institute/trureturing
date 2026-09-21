import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import Reg.Support.MapInjectiveRegistrationTemplates

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  companionPrefix := some `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }

namespace Reg.D5.S3.QuantumContext.ProjectionValuationObstruction

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.QuantumContext.ProjectionValuationObstruction

register_information_theorem _root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective in rayArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r))
  primitives rayRealization.toPrimitiveBundle realization ray_bridge
  variation ray_lawSensitive sensitivity ray_slotSensitive
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.QuantumContext.ProjectionValuationObstruction
example : _root_.Reg.D5.S3.QuantumContext.ProjectionValuationObstruction.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective.__information_unit.Statement =
    Function.Injective ksVectors := rfl
end

end Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
