import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary) (type_of% (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual.readout Reg.Support.LegacyRelations.Completion.actual.anchor)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completion_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(commutingCompletionArena)⟩,
  objectArena := .law ⟨(commutingCompletionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (commutingCompletionArena) (D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization) (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.instDecidableEqFourState D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization) ⟨(completion_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (completion_bridge) (@_root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.FourState D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.completionSignature D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.instDecidableEqFourState D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization)).Nonempty; decide),
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual.readout Reg.Support.LegacyRelations.Completion.actual.anchor),
  variation := .evidence ⟨(Reg.Support.LegacyRelations.Completion.finite_variation)⟩ (by first | exact (Reg.Support.LegacyRelations.Completion.finite_variation) | exact ⟨_, _, (Reg.Support.LegacyRelations.Completion.finite_variation)⟩),
  sensitivity := .evidence ⟨(Reg.Support.LegacyRelations.Completion.finite_sensitivity)⟩ (by exact (Reg.Support.LegacyRelations.Completion.finite_sensitivity)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["fn", "arg", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["arg", "arg", "fn", "fn", "fn", "arg", "fn", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := some ⟨_, ⟨(Reg.Support.LegacyRelations.Completion.registration)⟩⟩,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact1, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact2, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.descriptorFact, `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.liftedActualFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.statementExclusion,
  finiteLift := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.finiteLiftFacts,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.anchorEnumeration }

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
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completion_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary).Statement =
    (InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization.toTheoremUnit
      commutativity_hypothesis_is_necessary).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow


noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.arena
    D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CommutativityNecessaryStatement
    Reg.Support.LegacyRelations.Completion.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"commutativity_hypothesis_is_necessary\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.arena
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CommutativityNecessaryStatement
  Reg.Support.LegacyRelations.Completion.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout) where
  values := [D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF, D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG, D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation0 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature
    D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF PUnit.unit.{1}

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"commutativity_hypothesis_is_necessary\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [.function, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation1 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature
    D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG PUnit.unit.{1}

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"commutativity_hypothesis_is_necessary\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [.function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation2 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.Completion.signature
    D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.signature Reg.Support.LegacyRelations.Completion.actual
  D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut PUnit.unit.{1}

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observationFact2 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"commutativity_hypothesis_is_necessary\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"function\",\"function\",\"function\",\"argument\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"observation2\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [.argument, .argument, .function, .function, .function, .argument, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.observation2, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.varyingLaw : (r :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
      Reg.Support.LegacyRelations.Completion.signature) →
  Prop :=
  fun
    (r :
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
        Reg.Support.LegacyRelations.Completion.signature) =>
  And
    (Not
      (@Function.Commute.{0}
        (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Completion.signature Unit.unit)
        (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Completion.signature r
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF Unit.unit)
        (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Completion.signature r
          D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG Unit.unit)))
    (Not
      (@D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.KernelEquivalent.{0, 0, 0}
        (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
          Reg.Support.LegacyRelations.Completion.signature Unit.unit)
        (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
          (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit))
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit)))
        (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
          (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit))
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit)))
        (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
          (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit))
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit)))
        (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
          (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.PredictiveQuotient.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit))
          (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
            Reg.Support.LegacyRelations.Completion.signature r
            D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowG Unit.unit)
          (@D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient.predictiveProjection.{0, 0}
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature Unit.unit)
            (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.flowF
              Unit.unit)
            (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
              Reg.Support.LegacyRelations.Completion.signature r
              D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.CompletionReadout.cut
              Unit.unit)))))

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"commutativity_hypothesis_is_necessary\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange, declaration := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.Support.LegacyRelations.Completion.registration).actual (Reg.Support.LegacyRelations.Completion.registration).variation.2.choose (Reg.Support.LegacyRelations.Completion.registration).variation.1 (Reg.Support.LegacyRelations.Completion.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"Completion\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.Support.LegacyRelations.Completion, declaration := `Reg.Support.LegacyRelations.Completion.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.finiteLiftFacts : LeanInformationAudit.Contract.FiniteLiftFacts (D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena) (Reg.Support.LegacyRelations.Completion.arena) (@Reg.Support.LegacyRelations.Completion.fromLegacy) (@Reg.Support.LegacyRelations.Completion.toLegacy) where
  lowerLift := Reg.Support.LegacyRelations.Completion.to_from_legacy
  liftLower := Reg.Support.LegacyRelations.Completion.from_to_legacy
  law := by intro r; rw [Reg.Support.LegacyRelations.Completion.full_law_transport, Reg.Support.LegacyRelations.Completion.to_from_legacy]
  observations := []

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.liftedActual : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.Completion.signature :=
  Reg.Support.LegacyRelations.Completion.fromLegacy
  D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.completionRealization

noncomputable def Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.liftedActualFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"Completion\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Completion\",\"CommutingCompletionExchange\",\"TemplateShadow\",\"registration_1\",\"liftedActual\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.Support.LegacyRelations.Completion, declaration := `Reg.Support.LegacyRelations.Completion.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow.registration_1.liftedActual, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))
