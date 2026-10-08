import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
import Reg.Support.HughesIterationDepthNoGapRegistration



namespace Reg.D5.S1.Words.HughesIterationDepthNoGap

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
open _root_.D5.S1.Words.HughesIterationDepthNoGap
open LeanInformationAudit
open RegistrationTemplates

theorem _root_.Reg.D5.S1.Words.HughesIterationDepthNoGap.D5.S1.Words.HughesIterationDepthNoGap.result.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthNoGapArena (∀ (α : Type) [Finite.{1} α] (A B : D5.S1.Words.HughesIterationDepthNoGap.Language.{0} α) (r : Nat) (hr : @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) (@D5.S1.Words.HughesIterationDepthNoGap.iterationDepthSpectrumAt.{0} α D5.S1.Words.HughesIterationDepthNoGap.closedSourceZero A B) r) (q : Nat), @LE.le.{0} Nat instLENat q r → @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) (@D5.S1.Words.HughesIterationDepthNoGap.iterationDepthSpectrumAt.{0} α D5.S1.Words.HughesIterationDepthNoGap.closedSourceZero A B) q) D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthOriginRealization := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.HughesIterationDepthNoGap.result) (type_of% (depthOriginTemplate (fun origin => origin))) (type_of% (closedSourceZero)) (Unit) := {
  unitName := `Reg.D5.S1.Words.HughesIterationDepthNoGap.D5.S1.Words.HughesIterationDepthNoGap.result.__information_unit,
  realizationName := `Reg.D5.S1.Words.HughesIterationDepthNoGap.D5.S1.Words.HughesIterationDepthNoGap.result.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(depthNoGapArena)⟩,
  objectArena := .law ⟨(depthNoGapArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (depthNoGapArena) (depthOriginRealization) (depthOriginRealization.toPrimitiveBundle) ⟨(Reg.D5.S1.Words.HughesIterationDepthNoGap.D5.S1.Words.HughesIterationDepthNoGap.result.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (Reg.D5.S1.Words.HughesIterationDepthNoGap.D5.S1.Words.HughesIterationDepthNoGap.result.__primitive_realization) (@_root_.D5.S1.Words.HughesIterationDepthNoGap.result))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((depthOriginRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (depthOriginTemplate (fun origin => origin)),
  variation := .evidence ⟨(depth_law_variation)⟩ (by first | exact (depth_law_variation) | exact ⟨_, _, (depth_law_variation)⟩),
  sensitivity := .evidence ⟨(depth_slot_sensitivity)⟩ (by exact (depth_slot_sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (closedSourceZero),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S1.Words.HughesIterationDepthNoGap
