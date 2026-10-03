import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyRelations.Completion
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow



namespace Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow

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
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open InformationEscapeArenas.CommutingCompletionExchange

noncomputable def _root_.Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CommutativityNecessaryStatement D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completion_bridge D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) (type_of% (commutingCompletionArena)) (type_of% (commutingCompletionArena)) (type_of% (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual.readout Reg.Support.LegacyRelations.Completion.actual.anchor)) (type_of% (Reg.Support.LegacyRelations.Completion.finite_variation)) (type_of% (Reg.Support.LegacyRelations.Completion.finite_sensitivity)) (Unit) (Unit) (type_of% (Reg.Support.LegacyRelations.Completion.registration)) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completion_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(commutingCompletionArena)⟩,
  objectArena := ⟨(commutingCompletionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (commutingCompletionArena) (D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization) (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.instDecidableEqFourState D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization) ⟨(completion_bridge)⟩,
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual.readout Reg.Support.LegacyRelations.Completion.actual.anchor),
  variation := some ⟨(Reg.Support.LegacyRelations.Completion.finite_variation)⟩,
  sensitivity := some ⟨(Reg.Support.LegacyRelations.Completion.finite_sensitivity)⟩,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["arg", "arg", "fn", "fn", "fn", "arg", "fn", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := some ⟨(Reg.Support.LegacyRelations.Completion.registration)⟩,
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
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open InformationEscapeArenas.CommutingCompletionExchange
example : _root_.Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.__information_unit.Statement =
    (InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
      commutativity_hypothesis_is_necessary).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow
