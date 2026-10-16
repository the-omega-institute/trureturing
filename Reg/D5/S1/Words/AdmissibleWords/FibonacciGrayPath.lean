import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.AdmissibleWords.FibonacciGrayPath


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FibonacciGrayPath
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S1.Words.AdmissibleWords.FibonacciGrayPath
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev stageSignature := Reg.Support.SingleDependentReadout.signature Nat
  (fun d => Fin d → Bool) (fun _ => Bool)

def stageActual : Realization stageSignature :=
  realize stageSignature (fun _ d word => decide (Adm d word)) (fun e => nomatch e)
def stageRejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev stageArena : Arena where
  signature := stageSignature
  Law R := ∀ d h : Nat, h+1 ≤ Nat.fib (d+2) →
    ∃ word : Fin (h+1) → (Fin d → Bool), (∀ i, R.readout () d (word i) = true) ∧
      Function.Injective word ∧
      ∀ i : Fin h, hammingDist (word i.castSucc) (word i.succ) = 1

private theorem stageNegative : ¬ stageArena.Law stageRejected := by
  intro law
  obtain ⟨word, impossible, _⟩ := law 0 0 (by decide)
  cases impossible 0

def stageEvidence : Registration stageArena (type_of% (@exists_stage_path)) where
  actual := stageActual
  bridge := by simp [stageArena, stageActual, realize]
  variation := ⟨by simpa [stageActual, realize] using exists_stage_path, stageRejected, stageNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ stageNegative
  dependence := by
    intro i
    refine ⟨2, ![false,false], ![true,true], ?_⟩
    change decide (Adm 2 ![false,false]) ≠ decide (Adm 2 ![true,true])
    decide

def stage : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_stage_path) (Realization stageSignature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FibonacciGrayPath.exists_stage_path.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FibonacciGrayPath.stageEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨stageArena⟩
  objectArena := .source ⟨stageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stageArena ⟨stageEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature stageActual.readout stageActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FibonacciGrayPath
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","arg","body","fn","arg","body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms stageEvidence
#print axioms stage
end Reg.D5.S1.Words.AdmissibleWords.FibonacciGrayPath
