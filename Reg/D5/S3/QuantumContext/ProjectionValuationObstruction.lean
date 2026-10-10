import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import Reg.Support.MapInjectiveRegistrationTemplates



namespace Reg.D5.S3.QuantumContext.ProjectionValuationObstruction

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.QuantumContext.ProjectionValuationObstruction



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.ray_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(rayArena)⟩,
  objectArena := .law ⟨(rayArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (rayArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization) (rayRealization.toPrimitiveBundle) ⟨(ray_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (ray_bridge) (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((rayRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r)),
  variation := .evidence ⟨(ray_lawSensitive)⟩ (by first | exact (ray_lawSensitive) | exact ⟨_, _, (ray_lawSensitive)⟩),
  sensitivity := .evidence ⟨(ray_slotSensitive)⟩ (by exact (ray_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.QuantumContext.ProjectionValuationObstruction
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.ray_bridge.toTheoremUnit _root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective).Statement =
    Function.Injective ksVectors := rfl
end

end Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
