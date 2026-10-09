import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalExecutionBridge OriginalNarrowCost
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S0.Tower.DBonacci.Names

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def outputSignature : Signature where
  Params := {k : ℕ // 0 < k}
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (ZMod 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def outputActual : Realization outputSignature :=
  realize outputSignature
    (fun _ p w => NarrowWindowCost.output p.val p.property w)
    (fun e => nomatch e)

def outputRejected : Realization outputSignature :=
  realize outputSignature (fun _ _ _ => none) (fun e => nomatch e)

@[reducible] def outputArena : Arena where
  signature := outputSignature
  Law R := ∀ (k : ℕ) (hk : 0 < k) (w : List Bool),
    R.readout () ⟨k, hk⟩ w = endpointReading (OriginalRecord k hk w)

private theorem outputPositive : outputArena.Law outputActual := by
  intro k hk w
  exact output_record k hk w

private theorem outputNegative : ¬ outputArena.Law outputRejected := by
  intro law
  have impossible := law 3 (by decide) []
  cases impossible

def outputEvidence : Registration outputArena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record)) where
  actual := outputActual
  bridge := Iff.rfl
  variation := ⟨outputPositive, outputRejected, outputNegative⟩
  sensitivity := ⟨fun i => ⟨outputRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, outputNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨3, by decide⟩, [], [true], ?_⟩
    change NarrowWindowCost.output 3 (by decide) [] ≠
      NarrowWindowCost.output 3 (by decide) [true]
    have weight := dbonacci_add_two_of_lt 3 0 (by decide)
    simp [outputActual, realize, NarrowWindowCost.output, NarrowWindowCost.scanner,
      NarrowWindowCost.value, PartialDFA.eval, PartialDFA.evalFrom, runTransition, weight]

noncomputable def outputRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record)
    (type_of% (realize outputSignature outputActual.readout outputActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.output_record
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge/\
    Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.outputArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge.outputEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨outputArena⟩,
  objectArena := .source ⟨outputArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source outputArena ⟨outputEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize outputSignature outputActual.readout outputActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms outputEvidence

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
