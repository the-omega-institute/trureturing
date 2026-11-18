import D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal NNReal Classical
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming

namespace ResetReadyAfterFalse
abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n
  State p := Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => Function.update x p.2 false) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i : Fin n) (rest : List (Fin n))
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hlt : ∀ j ∈ rest, i.val < j.val)
    (hcover : ∀ j : Fin n, j ∉ insert i fixed → j ∈ rest)
    (hfar : ∀ j ∈ fixed, i.val < j.val → x j = y j),
    resetReady (insert i fixed) (R.readout () ⟨n, i⟩ x) (Function.update y i false)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) 0 [] ∅ (fun _ => false) (fun _ => false)
    (by simp) (by intro j hj; exact False.elim (hj (by simp [Subsingleton.elim j 0])))
    (by simp)
  obtain ⟨z, hz, _⟩ := hh
  change true = false at hz
  cases hz

def proof_record : Registration arena (type_of% @reset_ready_after_false) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reset_ready_after_false, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨2, 0⟩, (fun _ => false), (fun _ => true), ?_⟩
    intro he
    have hh := congrFun he (1 : Fin 2)
    change false = true at hh
    cases hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reset_ready_after_false) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming.reset_ready_after_false.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming.ResetReadyAfterFalse.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms proof_record
end ResetReadyAfterFalse

end Reg.D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming
