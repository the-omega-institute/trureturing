import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
import Reg.Support.MechanicalDyadicRegistration



noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration

open Set MeasureTheory
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq PhaseOutput := Classical.decEq _

def phaseClaim : Prop :=
  ∀ (alpha delta g : ℝ) (n : ℕ), 0 < n →
    0 ≤ alpha → alpha < 1 → 0 ≤ alpha + delta → alpha + delta < 1 →
    0 < g →
    (∀ k : Fin n,
      g ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha) ∧
      g ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha)) →
    (∀ i j : Fin n, i ≠ j →
      g ≤ |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
        Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) →
    (∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
      volume (jointMismatchSet alpha delta n u) =
        ENNReal.ofReal (∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta|)) ∧
    ((n : ℝ) * |delta| ≤ g / 4 →
      (∀ k : Fin (n + 1),
        |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| ≤ g / 4) ∧
      volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) =
        ENNReal.ofReal (|delta| * (((n + 1)^2 / 4 : ℕ) : ℝ)) ∧
      ∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
        volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) ≤
          volume (jointMismatchSet alpha delta n u))

theorem phaseBridge : LegacyPrimitiveRealization phaseArena.toPrimitiveLawArena
    phaseClaim phaseRealization := by
  constructor
  exact Iff.rfl

def phaseBad : PrimitiveRealization phaseArena.signature :=
  @mechanicalReadoutRealization PhaseOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ _ _ => (1 : ENNReal))

private theorem phaseBad_not_law : ¬ phaseArena.Law phaseBad := by
  intro h
  have hfract : Int.fract (1 / 2 : ℝ) = 1 / 2 :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hcuts : ∀ k : Fin 1,
      (1 / 2 : ℝ) ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) ∧
      (1 / 2 : ℝ) ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) := by
    intro k
    have hk : k.val = 0 := by omega
    norm_num [hk, hfract]
  have hgaps : ∀ i j : Fin 1, i ≠ j →
      (1 / 2 : ℝ) ≤
        |Int.fract (((i.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) -
          Int.fract (((j.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ))| := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hmove : ∀ k : Fin (1 + 1),
      |(0 : ℝ) + (k.val : ℝ) * 0| ≤ (1 / 2 : ℝ) / 4 := by
    intro k
    norm_num
  have heq := (h (1 / 2) 0 (1 / 2) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcuts hgaps).1 0 hmove
  simp [phaseBad, mechanicalReadoutRealization] at heq

theorem phaseVariation : phaseArena.Law phaseRealization ∧
    ¬ phaseArena.Law phaseBad := by
  exact ⟨phaseBridge.equivalence.mp
    (fun alpha delta g n hn ha0 ha1 hb0 hb1 hg hcuts hgaps =>
      joint_phase_calibration_law alpha delta g n hn ha0 ha1 hb0 hb1 hg hcuts hgaps),
    phaseBad_not_law⟩

theorem phaseSensitivity : FiniteSlotSensitivity phaseArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨phaseRealization, phaseBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => phaseBad_not_law, fun _ => phaseVariation.1⟩
  · intro i
    exact Fin.elim0 i

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law) (type_of% (@mechanicalReadoutRealization PhaseOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.phaseReadout))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.phaseBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(phaseArena)⟩,
  objectArena := .object ⟨(phaseArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseRealization) (phaseRealization.toPrimitiveBundle) ⟨(phaseBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (phaseBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((phaseRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization PhaseOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.phaseReadout)),
  variation := .evidence ⟨(phaseVariation)⟩ (by first | exact (phaseVariation) | exact ⟨_, _, (phaseVariation)⟩),
  sensitivity := .evidence ⟨(phaseSensitivity)⟩ (by exact (phaseSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration


noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalPhaseCalibration\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalPhaseCalibration\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalPhaseCalibration\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalPhaseCalibration\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
