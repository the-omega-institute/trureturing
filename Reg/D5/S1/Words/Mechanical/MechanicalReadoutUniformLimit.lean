import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration



noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit

open Set Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : DecidableEq CompletionOutput := Classical.decEq _

theorem uniformBridge : LegacyPrimitiveRealization uniformBoundArena.toPrimitiveLawArena
    (uniformBoundClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

def badCompletion : PrimitiveRealization uniformBoundArena.signature :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => ((fun _ _ _ => (0 : ℝ)), (fun _ _ _ _ => (0 : ℝ))))

theorem uniformVariation : uniformBoundArena.Law completionRealization ∧
    ¬ uniformBoundArena.Law badCompletion := by
  constructor
  · apply uniformBridge.equivalence.mp
    intro r alpha x hr0 hr1 ha
    exact geometric_readout_uniform_slope_bound r alpha x hr0 hr1 ha
  · intro h
    have hbad := (h (1 / 2) (3 / 4) 0 (by norm_num) (by norm_num)
      (by norm_num [Set.mem_Ico])).1
    norm_num [badCompletion, mechanicalReadoutRealization] at hbad

theorem uniformSensitivity : FiniteSlotSensitivity uniformBoundArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => uniformVariation.2, fun _ => uniformVariation.1⟩
  · intro i
    exact Fin.elim0 i

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound) (type_of% (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.uniformBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(uniformBoundArena)⟩,
  objectArena := .object ⟨(uniformBoundArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.completionRealization) (completionRealization.toPrimitiveBundle) ⟨(uniformBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (uniformBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((completionRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion)),
  variation := .evidence ⟨(uniformVariation)⟩ (by first | exact (uniformVariation) | exact ⟨_, _, (uniformVariation)⟩),
  sensitivity := .evidence ⟨(uniformSensitivity)⟩ (by exact (uniformSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit


noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutUniformLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutUniformLimit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutUniformLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutUniformLimit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
