import Reg.Support.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.LegacyRelations.System
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit



namespace Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
attribute [local instance]
  contextDecidableEq
  modelDecidableEq
local instance systemArenaStateDecidableEq : DecidableEq arena.toArena.State :=
  arena.toArena.stateDecidableEq

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application) (type_of% (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.System.signature Reg.Support.LegacyRelations.System.actual.readout Reg.Support.LegacyRelations.System.actual.anchor)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.system_self_application_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(arena)⟩,
  objectArena := .law ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization) (@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.Arena.State.{0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena)) (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena) Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemArenaStateDecidableEq D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization) ⟨(system_self_application_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (system_self_application_realization) (@_root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((@D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle.{0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.Arena.State.{0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena)) (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena) Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemArenaStateDecidableEq D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization)).Nonempty; decide),
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.System.signature Reg.Support.LegacyRelations.System.actual.readout Reg.Support.LegacyRelations.System.actual.anchor),
  variation := .evidence ⟨(Reg.Support.LegacyRelations.System.finite_variation)⟩ (by first | exact (Reg.Support.LegacyRelations.System.finite_variation) | exact ⟨_, _, (Reg.Support.LegacyRelations.System.finite_variation)⟩),
  sensitivity := .evidence ⟨(Reg.Support.LegacyRelations.System.finite_sensitivity)⟩ (by exact (Reg.Support.LegacyRelations.System.finite_sensitivity)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, definition := some { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, name := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.SystemStatement, path := #[] }, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := some ⟨_, ⟨(Reg.Support.LegacyRelations.System.registration)⟩⟩,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.SystemStatement, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.descriptorFact, `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.liftedActualFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.statementExclusion,
  finiteLift := some `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.finiteLiftFacts,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.anchorEnumeration }

end

end Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit

namespace Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
open LeanInformationAudit.Contract

noncomputable def finiteLiftFacts : FiniteLiftFacts
    _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
    _root_.Reg.Support.LegacyRelations.System.arena
    _root_.Reg.Support.LegacyRelations.System.fromLegacy
    _root_.Reg.Support.LegacyRelations.System.toLegacy where
  lowerLift := _root_.Reg.Support.LegacyRelations.System.to_from_legacy
  liftLower := _root_.Reg.Support.LegacyRelations.System.from_to_legacy
  law := by
    intro r
    rw [_root_.Reg.Support.LegacyRelations.System.full_law_transport,
      _root_.Reg.Support.LegacyRelations.System.to_from_legacy]
  observations := []

end Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit


noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena
noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.Support.LegacyRelations.System.arena) (Reg.Support.LegacyRelations.System.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"engine_census_self_application\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.Support.LegacyRelations.System.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) where
  values := [(fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
    (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.observation0 : (stage :
    D5.S3.ConceptDynamics.InformationEscape.Arena.State.{0}
      (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0}
        D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena)) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.System.signature
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    PUnit.unit.{1} :=
  fun
    (stage :
      D5.S3.ConceptDynamics.InformationEscape.Arena.State.{0}
        (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0}
          D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.Support.LegacyRelations.System.signature Reg.Support.LegacyRelations.System.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (nat_lit 0)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    PUnit.unit.{1} stage

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"SystemStatement\"],\"part\":\"value\",\"path\":[\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.SystemStatement, part := .value, path := [.function, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.varyingLaw : (r :
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
      Reg.Support.LegacyRelations.System.signature) →
  Prop :=
  fun
    (r :
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
        Reg.Support.LegacyRelations.System.signature) =>
  D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.Law.{0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena (Reg.Support.LegacyRelations.System.toLegacy r)

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"engine_census_self_application\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.Support.LegacyRelations.System.registration).actual (Reg.Support.LegacyRelations.System.registration).variation.2.choose (Reg.Support.LegacyRelations.System.registration).variation.1 (Reg.Support.LegacyRelations.System.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"System\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.Support.LegacyRelations.System, declaration := `Reg.Support.LegacyRelations.System.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.finiteLiftFacts : LeanInformationAudit.Contract.FiniteLiftFacts (D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena) (Reg.Support.LegacyRelations.System.arena) (@Reg.Support.LegacyRelations.System.fromLegacy) (@Reg.Support.LegacyRelations.System.toLegacy) where
  lowerLift := Reg.Support.LegacyRelations.System.to_from_legacy
  liftLower := Reg.Support.LegacyRelations.System.from_to_legacy
  law := by intro r; rw [Reg.Support.LegacyRelations.System.full_law_transport, Reg.Support.LegacyRelations.System.to_from_legacy]
  observations := []

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.liftedActual : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.{0, 0, 0, 0, 0}
  Reg.Support.LegacyRelations.System.signature :=
  Reg.Support.LegacyRelations.System.fromLegacy D5.S3.ConceptDynamics.InformationEscape.SystemUnit.systemRealization

noncomputable def Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.liftedActualFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyRelations\",\"System\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SystemUnit\",\"registration_1\",\"liftedActual\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.Support.LegacyRelations.System, declaration := `Reg.Support.LegacyRelations.System.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit, declaration := `Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.registration_1.liftedActual, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))
