import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-domain support observations and source-bound variation. -/

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private constantTable score_le_support from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
noncomputable section
open scoped BigOperators

abbrev Parameters := {L : ℕ // 3 ≤ L}

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => FullScore p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => support true y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (hL : 3 ≤ L) (y : FullScore L), EarlyPair y →
    highLower hL y ≤ R.readout () ⟨L,hL⟩ y - inputAnchor hL y

private def terminalScore (L : ℕ) (t : ℝ) (ht : 0 ≤ t) : FullScore L where
  A := fun _ => 0
  C := fun _ => 0
  P := fun _ => 0
  T := t
  nonnegA := by simp
  nonnegC := by simp
  nonnegP := by simp
  nonnegT := ht
  terminalA := rfl
  terminalC := rfl
  terminalP := rfl

private theorem terminal_score (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Word L → Fin (L + 1)) :
    score (terminalScore L t ht) f = if f (fun _ => true) = 0 then t else 0 := by
  classical
  unfold score
  have hr (b : Word L) : reward (terminalScore L t ht) b (f b) =
      if b = (fun _ => true) then (if f b = 0 then t else 0) else 0 := by
    refine Fin.cases ?_ (fun i => ?_) (f b)
    · simp [reward,baseline,terminalScore]
    · simp [reward,numerical,terminalScore,Fin.succ_ne_zero]
  simp_rw [hr]
  simp

private theorem terminal_support (L : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    support true (terminalScore L t ht) = t := by
  classical
  apply le_antisymm
  · unfold support
    apply Finset.sup'_le
    intro f _
    rw [terminal_score]
    split <;> linarith
  · have h := score_le_support true (terminalScore L t ht) (constantTable true L 0)
    simpa [terminal_score,constantTable] using h

private theorem positive : arena.Law actual := @arbitrary_input_lower_bound
private theorem faithful_bridge :
    (type_of% (@arbitrary_input_lower_bound)) ↔ arena.Law actual := Iff.rfl

private theorem negative : ¬arena.Law rejected := by
  intro h
  have h := h 3 (by omega) (terminalScore 3 0 le_rfl) (by intro b i hi hlate; rfl)
  have hn : 0 ≤ highLower (by omega) (terminalScore 3 0 le_rfl) :=
    (le_max_left 0 _).trans (le_max_left _ _)
  change highLower (by omega) (terminalScore 3 0 le_rfl) ≤
    -1 - inputAnchor (by omega) (terminalScore 3 0 le_rfl) at h
  have hz : inputAnchor (by omega) (terminalScore 3 0 le_rfl) = 0 := by
    simp [inputAnchor,early,gamma,pairTotal,terminalScore]
  rw [hz,sub_zero] at h
  linarith

def evidence : Registration arena (type_of% (@arbitrary_input_lower_bound)) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive,rejected,negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨⟨3,by omega⟩, terminalScore 3 0 le_rfl, terminalScore 3 1 (by norm_num), ?_⟩
    change support true (terminalScore 3 0 le_rfl) ≠
      support true (terminalScore 3 1 (by norm_num))
    rw [terminal_support,terminal_support]
    norm_num

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@arbitrary_input_lower_bound)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.arbitrary_input_lower_bound,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ y => support true y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain,
    definition := none, coordinates := #[0,2],
    readouts := #[{
      path := #["body","body","body","body","arg","fn","arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms faithful_bridge
#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
