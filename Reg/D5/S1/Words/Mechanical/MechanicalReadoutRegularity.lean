import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration



noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity

open Set
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : DecidableEq CompletionOutput := Classical.decEq _

theorem regularityBridge : LegacyPrimitiveRealization regularityArena.toPrimitiveLawArena
    (regularityClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

def badCompletion : PrimitiveRealization regularityArena.signature :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => ((fun _ _ _ => (0 : ℝ)), (fun _ _ _ _ => (0 : ℝ))))

theorem regularityVariation : regularityArena.Law completionRealization ∧
    ¬ regularityArena.Law badCompletion := by
  constructor
  · apply regularityBridge.equivalence.mp
    intro r alpha x hr0 hr1 ha
    exact geometric_readout_continuity_and_jump r alpha x hr0 hr1 ha
  · intro h
    have hiff := (h (1 / 2) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num [Set.mem_Ioo])).1
    have hcontinuous :
        ∀ eps : ℝ, 0 < eps → ∃ radius : ℝ, 0 < radius ∧
          ∀ beta : ℝ, |beta - (1 / 2 : ℝ)| < radius →
            |(badCompletion.readout () ()).1 (1 / 2) beta (1 / 2) -
              (badCompletion.readout () ()).1 (1 / 2) (1 / 2) (1 / 2)| < eps := by
      intro eps heps
      refine ⟨1, by norm_num, ?_⟩
      intro beta _
      simpa [badCompletion, mechanicalReadoutRealization] using heps
    have hno := hiff.mp hcontinuous
    have hneq := hno 1 (by norm_num) 1
    apply hneq
    norm_num

theorem regularitySensitivity : FiniteSlotSensitivity regularityArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => regularityVariation.2, fun _ => regularityVariation.1⟩
  · intro i
    exact Fin.elim0 i

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump) (type_of% (regularityArena)) (type_of% (regularityArena)) (type_of% (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion))) (type_of% (regularityVariation)) (type_of% (regularitySensitivity)) (type_of% (ℝ)) (Unit) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.regularityBridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(regularityArena)⟩,
  objectArena := ⟨(regularityArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.regularityArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.completionRealization) (completionRealization.toPrimitiveBundle) ⟨(regularityBridge)⟩,
  readout := some (@mechanicalReadoutRealization CompletionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion)),
  variation := some ⟨(regularityVariation)⟩,
  sensitivity := some ⟨(regularitySensitivity)⟩,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
