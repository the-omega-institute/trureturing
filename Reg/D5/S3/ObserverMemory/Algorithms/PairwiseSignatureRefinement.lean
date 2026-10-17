import Batteries.Tactic.OpenPrivate
import D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private labelsAt_correct from D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement

namespace Reg.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
noncomputable section

@[reducible] def signature : Signature where
  Params := Σ n : Nat, Σ k : Nat, Σ O : Type,
    (Fin k → Fin n → Fin n) × (Fin n → O)
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.2.1) → p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => controlledBehavior p.2.2.2.1 p.2.2.2.2 x)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p x => if h : 0 < p.1 then
    controlledBehavior p.2.2.2.1 p.2.2.2.2 ⟨0,h⟩ else
    controlledBehavior p.2.2.2.1 p.2.2.2.2 x)
  (fun e => nomatch e)

/-- The complete theorem telescope and every cost and execution conjunct remain. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {n k : Nat} (hn : 0 < n)
    {O : Type} [DecidableEq O] (F : Fin k → Fin n → Fin n) (o : Fin n → O),
    ∃ h cost c, h ≤ n - initialClasses o ∧ Terminates F o h cost c ∧
      (∀ x y, c x = c y ↔ R.readout () ⟨n,k,O,F,o⟩ x = R.readout () ⟨n,k,O,F,o⟩ y) ∧
      (∀ x y, R.readout () ⟨n,k,O,F,o⟩ x ≠ R.readout () ⟨n,k,O,F,o⟩ y →
        ∃ w : List (Fin k), w.length ≤ n - initialClasses o ∧
          o (runWord F w x) ≠ o (runWord F w y)) ∧
      cost = 4*n*n+n + (h+1)*(n*n*(7*k+8)+n) ∧
      cost ≤ 14*(k+1)*n*n*(n-initialClasses o+1)

private theorem positive : arena.Law actual := pairwise_signature_termination

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let F : Fin 0 → Fin 2 → Fin 2 := fun a => Fin.elim0 a
  let o : Fin 2 → Bool := fun x => decide (x = 1)
  obtain ⟨h,cost,c,_,ht,hc,_⟩ := law (n := 2) (k := 0) (by decide) F o
  have equal : c 0 = c 1 := (hc 0 1).mpr rfl
  rw [ht.1] at equal
  have same := (labelsAt_correct F o h 0 1).mp equal
  have impossible := same [] (Nat.zero_le h)
  change false = true at impossible
  cases impossible

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement.pairwise_signature_termination)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive,rejected,negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨2,0,Bool,(fun a => Fin.elim0 a),(fun x => decide (x = 1))⟩,0,1,?_⟩
    intro same
    have impossible := congrFun same []
    change false = true at impossible
    cases impossible

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement.pairwise_signature_termination)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement.pairwise_signature_termination
    "Reg.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement/arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement,
    definition := none, coordinates := #[0,1,3,5,6],
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","arg","arg","fn","arg",
        "body","body","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false },{
      path := #["body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","arg","arg","fn","arg",
        "body","body","arg","arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false },{
      path := #["body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","arg","arg","arg","fn","arg",
        "body","body","domain","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false },{
      path := #["body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","arg","arg","arg","fn","arg",
        "body","body","domain","arg","arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.ObserverMemory.Algorithms.PairwiseSignatureRefinement
