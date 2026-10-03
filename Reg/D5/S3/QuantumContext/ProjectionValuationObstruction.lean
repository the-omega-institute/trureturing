import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
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

noncomputable def _root_.Reg.D5.S3.QuantumContext.ProjectionValuationObstruction.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena (@Function.Injective.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))) D5.S3.QuantumContext.ProjectionValuationObstruction.KSVector D5.S3.QuantumContext.ProjectionValuationObstruction.ksVectors) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.ray_bridge D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective) (type_of% (rayArena)) (type_of% (rayArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r))) (type_of% (ray_lawSensitive)) (type_of% (ray_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.ray_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(rayArena)⟩,
  objectArena := ⟨(rayArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (rayArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayRealization) (rayRealization.toPrimitiveBundle) ⟨(ray_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization (Fin 18) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.RayCode (instDecidableEqFin D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayCardinality) (fun r => D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayReadout r)),
  variation := some ⟨(ray_lawSensitive)⟩,
  sensitivity := some ⟨(ray_slotSensitive)⟩,
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
example : _root_.Reg.D5.S3.QuantumContext.ProjectionValuationObstruction.D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective.__information_unit.Statement =
    Function.Injective ksVectors := rfl
end

end Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
