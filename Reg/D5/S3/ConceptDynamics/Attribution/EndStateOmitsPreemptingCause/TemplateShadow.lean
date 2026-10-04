import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyRelations.Preemption
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow



namespace Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open InformationEscapeArenas.EndStateOmitsPreemptingCause



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause) (type_of% (endStateOmitsPreemptingCauseArena)) (type_of% (endStateOmitsPreemptingCauseArena)) (type_of% (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual.readout Reg.Support.LegacyRelations.Preemption.actual.anchor)) (type_of% (Reg.Support.LegacyRelations.Preemption.finite_variation)) (type_of% (Reg.Support.LegacyRelations.Preemption.finite_sensitivity)) (Unit) (Unit) (type_of% (Reg.Support.LegacyRelations.Preemption.registration)) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.preemption_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(endStateOmitsPreemptingCauseArena)⟩,
  objectArena := ⟨(endStateOmitsPreemptingCauseArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (endStateOmitsPreemptingCauseArena) (D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.preemptionRealization) (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.preemptionSignature (fun (a b : D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.PreemptionTrace) => @Fintype.decidablePiFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (a_1 b : Option.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) => @Option.instDecidableEq.{0} D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.instDecidableEqMechanism a_1 b) (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b) D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.preemptionRealization) ⟨(preemption_bridge)⟩,
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Preemption.signature Reg.Support.LegacyRelations.Preemption.actual.readout Reg.Support.LegacyRelations.Preemption.actual.anchor),
  variation := some ⟨(Reg.Support.LegacyRelations.Preemption.finite_variation)⟩,
  sensitivity := some ⟨(Reg.Support.LegacyRelations.Preemption.finite_sensitivity)⟩,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }, { path := #["arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := some ⟨(Reg.Support.LegacyRelations.Preemption.registration)⟩,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open InformationEscapeArenas.EndStateOmitsPreemptingCause
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.preemption_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause).Statement =
    (InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization.toTheoremUnit
      end_state_omits_preempting_cause).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
