import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge WindowChargeInverse
open ForcedThresholdPrefix
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ Q : ℕ, Σ m : ℕ, Σ a : ℕ,
    Σ _labels : ZMod (Q * m + 1) → Y, Y × Y × Y
  State p := Option (LiveRecord (p.2.1 * p.2.2.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p => initialLabel (p.2.1 * p.2.2.1) p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ p _ => p.2.2.2.2.2.2.2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀  {Y : Type u} (Q m a : ℕ) (hQ : 2 ≤ Q)
    (ha : 3 ≤ a) (ham : a < m) (alphabet : Bool)
    (labels : ZMod (Q * m + 1) → Y) (outside rejected bottom : Y)
    (different : outside ≠ rejected) (v : ZMod 2)
    (π : NarrowWindowCost.Selector m Y)
    (correct : ∀ history : List (AllowedBlock (Q * m) m alphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      NarrowWindowCost.output (Q * m) (by nlinarith) w = some v →
      ∃ budget c, NarrowWindowCost.execute (Q * m) (by nlinarith) π budget w (some v) [] =
        some (R.readout () ⟨Y, Q, m, a, labels, outside, rejected, bottom⟩
          (OriginalRecord (Q * m) (by nlinarith) w), c)),
    ∃ B rest, π (some v) [] = .inr B ∧
      List.ofFn B = List.replicate a true ++ false :: rest ∧
      ∀ phase s, s < Q * m →
        runBits (Q * m) B (some ⟨v, phase, s⟩) =
          if s < Q * m - a then
            some ⟨v + wordIncrement (Q * m) phase B,
              phase + (m : ℕ), tailAfter 0 B⟩ else none

private theorem positive : arena.{u}.Law actual :=
  @_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix.forced_threshold_root.{u}

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let lo : ULift.{u} Bool := ⟨false⟩
  let hi : ULift.{u} Bool := ⟨true⟩
  let π : NarrowWindowCost.Selector 4 (ULift.{u} Bool) := fun _ _ => .inl lo
  have correct : ∀ history : List (AllowedBlock 8 4 false),
      let w := history.flatMap (fun action => List.ofFn action.val)
      NarrowWindowCost.output 8 (by decide) w = some 0 →
      ∃ budget c, NarrowWindowCost.execute 8 (by decide) π budget w (some 0) [] =
        some (rejected.readout () ⟨ULift.{u} Bool, 2, 4, 3, (fun _ => lo), lo, hi, lo⟩
          (OriginalRecord 8 (by decide) w), c) := by
    intro history
    dsimp only
    intro free
    exact ⟨0, 0, rfl⟩
  obtain ⟨B, rest, impossible, _⟩ := law 2 4 3 (by decide) (by decide)
    (by decide) false (fun _ => lo) lo hi lo (by decide) 0 π correct
  change (Sum.inl lo : ULift.{u} Bool ⊕ (Fin 4 → Bool)) = Sum.inr B at impossible
  cases impossible

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix.forced_threshold_root.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨ULift.{u} Bool, 2, 4, 3, (fun _ => ⟨false⟩),
      ⟨false⟩, ⟨true⟩, ⟨false⟩⟩, none, some ⟨0, 0, 5⟩, ?_⟩
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix.forced_threshold_root.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix.forced_threshold_root.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix,
    definition := none,
    coordinates := #[0, 1, 2, 3, 8, 9, 10, 11],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ForcedThresholdPrefix
