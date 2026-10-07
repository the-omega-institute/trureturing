import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
import D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
import Reg.Support.PointwiseEqualityRegistrations



noncomputable section
namespace Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage

open Set MeasureTheory
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq PhaseAverageOutput := Classical.decEq _
local instance : DecidableEq phaseAverageArena.State := phaseAverageArena.toArena.stateDecidableEq

def phaseAverageClaim : Prop :=
  ∀ (r : ℝ), 0 < r → r < 1 → ∀ (A : Set ℝ), MeasurableSet A →
    A ⊆ Set.Icc (0 : ℝ) 1 →
      ∫⁻ x in Set.Ico (0 : ℝ) 1, geometricAtomicMeasure r x A ∂volume = volume A

theorem phaseAverageBridge : LegacyPrimitiveRealization phaseAverageArena.toPrimitiveLawArena
    phaseAverageClaim phaseAverageRealization := by
  constructor
  constructor
  · intro h
    change ∀ _ : Unit, phaseAverageIntegral = phaseAverageVolume
    intro _
    funext input
    exact h input.ratio input.ratioPositive input.ratioBelowOne input.target
      input.targetMeasurable input.targetInUnit
  · intro h r hr0 hr1 A hA hAunit
    have hFunctions : phaseAverageIntegral = phaseAverageVolume := by
      exact h ()
    exact congrFun hFunctions ⟨r, hr0, hr1, A, hA, hAunit⟩

def phaseAverageBad :
    PrimitiveRealization (homogeneousPointwiseEqSignature Unit PhaseAverageOutput) :=
  homogeneousPointwiseEqRealization
    (fun _ : Unit => (fun _ : PhaseAverageInput => (0 : ENNReal)))
    (fun _ : Unit => (fun _ : PhaseAverageInput => (1 : ENNReal)))

private def emptyInput : PhaseAverageInput where
  ratio := 1 / 2
  ratioPositive := by norm_num
  ratioBelowOne := by norm_num
  target := ∅
  targetMeasurable := MeasurableSet.empty
  targetInUnit := Set.empty_subset _

theorem phaseAverageVariation : phaseAverageArena.Law phaseAverageRealization ∧
    ¬ phaseAverageArena.Law phaseAverageBad := by
  constructor
  · exact phaseAverageBridge.equivalence.mp geometric_atomic_phase_average
  · intro h
    have hh := congrFun (h ()) emptyInput
    exact zero_ne_one hh

theorem phaseAverageSensitivity : FiniteSlotSensitivity phaseAverageArena.toPrimitiveLawArena := by
  change FiniteSlotSensitivity
    (homogeneousPointwiseEqArena (Arena.ofFintype Unit) PhaseAverageOutput)
  have hne : (fun _ : PhaseAverageInput => (0 : ENNReal)) ≠
      (fun _ : PhaseAverageInput => (1 : ENNReal)) := by
    intro h
    exact zero_ne_one (congrFun h emptyInput)
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := fun _ : PhaseAverageInput => (0 : ENNReal))
    (b := fun _ : PhaseAverageInput => (1 : ENNReal)) hne

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average) (type_of% (@homogeneousPointwiseEqRealization Unit PhaseAverageOutput
    (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageIntegral)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageVolume))) (type_of% (Set.{0} ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.phaseAverageBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(phaseAverageArena)⟩,
  objectArena := .object ⟨(phaseAverageArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageRealization) (phaseAverageRealization.toPrimitiveBundle) ⟨(phaseAverageBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (phaseAverageBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((phaseAverageRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@homogeneousPointwiseEqRealization Unit PhaseAverageOutput
    (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageIntegral)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageVolume)),
  variation := .evidence ⟨(phaseAverageVariation)⟩ (by first | exact (phaseAverageVariation) | exact ⟨_, _, (phaseAverageVariation)⟩),
  sensitivity := .evidence ⟨(phaseAverageSensitivity)⟩ (by exact (phaseAverageSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (Set.{0} ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage


noncomputable def Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena
noncomputable def Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"Atomic\",\"MechanicalReadoutPhaseAverage\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"Atomic\",\"MechanicalReadoutPhaseAverage\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena
noncomputable def Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"Atomic\",\"MechanicalReadoutPhaseAverage\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"Atomic\",\"MechanicalReadoutPhaseAverage\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage, declaration := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
