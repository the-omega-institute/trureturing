import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open OriginalAcquiredTrace GlobalPresetObstruction DonorCorrection FourLabelPaidFeedback
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := ℕ
  State m := Option (LiveRecord (2 * m - 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m q => presetFee m q) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 4) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (alphabet : Bool) (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = labels (phaseClass m j)),
    (∀ v, OriginalFiberCost (2 * m - 2) m (by omega) alphabet f v = 2 ∧
      FiberPresetPrice (2 * m - 2) m (by omega) alphabet f v = 3) ∧
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = 2 ∧
    SelectedPresetPrice (2 * m - 2) m (by omega) alphabet f = 3 ∧
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = 3 ∧
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      (∃ issued, PaidTrace (adaptiveSelector m labels (f none)) free q [] issued (f q) ∧
        issued.length = (if q.isSome then 2 else 0) ∧
        (archiveWords issued).length = (if q.isSome then 2 * m else 0)) ∧
      (∃ issued, PaidTrace (presetSelector (commonStream m) (commonStop labels (f none)))
        free q [] issued (f q) ∧ issued.length = R.readout () m q ∧
        (archiveWords issued).length = presetFee m q * m)) ∧
    ∀ v : ZMod 2, ∃ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      q = some ⟨v, -1, 0⟩ ∧ ∃ ad pre,
        PaidTrace (adaptiveSelector m labels (f none)) free q [] ad (f q) ∧
        (archiveWords ad).length = 2 * m ∧
        PaidTrace (presetSelector (commonStream m) (commonStop labels (f none)))
          free q [] pre (f q) ∧ (archiveWords pre).length = 3 * m

private theorem positive : arena.{u}.Law actual := original_four_label_paid_feedback

def sampleTarget : Option (LiveRecord 8) → ULift.{u} (Fin 4)
  | none => ⟨0⟩
  | some q => ⟨phaseClass 5 (-q.phase)⟩

private theorem sample_target : ∀ (v : ZMod 2) (j : ZMod 9) (s : ℕ), s < 8 →
    sampleTarget.{u} (some ⟨v, -j, s⟩) = (ULift.up (phaseClass 5 j) : ULift.{u} (Fin 4)) := by
  intros
  simp [sampleTarget]

private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law 5 (by omega) false (fun c => (ULift.up c : ULift.{u} (Fin 4)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
  obtain ⟨issued, _, count, bits⟩ := (bad.2.2.2.2.2.2.1 []).2
  change issued.length = 4 at count
  have size := archive_length issued
  rw [count] at size
  rw [size] at bits
  have empty : OriginalRecord 8 (by omega) [] = some ⟨0, 0, 0⟩ := rfl
  norm_num only [List.flatMap_nil] at bits
  rw [empty] at bits
  norm_num [presetFee, phaseClass] at bits

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback.original_four_label_paid_feedback.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨5, none, some ⟨0, 0, 0⟩, ?_⟩
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback.original_four_label_paid_feedback.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback.original_four_label_paid_feedback
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback
