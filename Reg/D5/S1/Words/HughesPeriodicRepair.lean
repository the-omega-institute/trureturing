import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.HughesPeriodicRepair
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.HughesPeriodicRepair

open _root_.D5.S1.Words.HughesBlockExchange
open _root_.D5.S1.Words.HughesUnaryInsertion
open _root_.D5.S1.Words.UnaryGapWords
open _root_.D5.S1.Words.Powers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ α : Type u, α × Nat × Nat × Nat × Nat
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := WithTop Nat
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (A B : α), A ≠ B → ∀ H J K L : Nat,
    R.readout () ⟨α,A,H,J,K,L⟩ B = ((2 : Nat) : WithTop Nat)

def actual : Realization signature.{u} :=
  realize signature (fun _ p B =>
    degree
      (wordPower p.2.2.1 [p.2.1,B,p.2.1] ++ [p.2.1,B,p.2.1,B,p.2.1] ++
        wordPower p.2.2.2.1 [p.2.1,B,p.2.1])
      (wordPower ((p.2.2.2.2.1+1)+(p.2.2.2.2.2+1)) [p.2.1,B,p.2.1])
      (wordPower p.2.2.2.2.1 [p.2.1,B,p.2.1] ++ [p.2.1,B] ++
        wordPower (p.2.2.1+1) [p.2.1,B,p.2.1] ++ [p.2.1] ++
        wordPower (p.2.2.2.2.2+1) [p.2.1,B,p.2.1] ++ [B,p.2.1] ++
        wordPower p.2.2.2.1 [p.2.1,B,p.2.1])) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => Empty.elim e)

private def a : ULift.{u} Bool := ⟨false⟩
private def b : ULift.{u} Bool := ⟨true⟩

private theorem rejected_law : ¬arena.{u}.Law rejected := by
  intro h
  have he := h a b (by simp [a,b]) 0 0 0 0
  change (⊤ : WithTop Nat) = ((2 : Nat) : WithTop Nat) at he
  simp at he

private theorem actual_dependence :
    actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ a ≠
      actual.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ b := by
  have h₁ := (inserted_degree a 5 [] [6] [5] (by simp) rfl rfl rfl).2
  have h₂ := _root_.D5.S1.Words.HughesPeriodicRepair.shifted_successor_degree
    a b (by simp [a,b]) 0 0 0 0
  have e₁ : actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ a =
      ((1 : Nat) : WithTop Nat) := by
    simpa [actual,realize,wordPower,gap,occupied,List.replicate_succ] using h₁
  have e₂ : actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ b =
      ((2 : Nat) : WithTop Nat) := by
    simpa [actual,realize] using h₂
  rw [e₁,e₂]
  norm_num

def source_registration : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.HughesPeriodicRepair.shifted_successor_degree.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.HughesPeriodicRepair.shifted_successor_degree.{u},
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Bool,a,0,0,0,0⟩,a,b,actual_dependence⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.HughesPeriodicRepair.shifted_successor_degree.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S1.Words.HughesPeriodicRepair.shifted_successor_degree.__information_unit
  realizationName := `Reg.D5.S1.Words.HughesPeriodicRepair.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.HughesPeriodicRepair
    definition := none
    coordinates := #[0,1,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

namespace Repair

open _root_.D5.S1.Words.HughesPeriodicRepair

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (A B : α), A≠B → ∀ H J K L : Nat,
    let a := wordPower H [A,B,A] ++ [A,B]
    let c := [B,A] ++ wordPower J [A,B,A]
    let p := wordPower (K+1) [A,B,A]
    let q := wordPower (L+1) [A,B,A]
    let x := wordPower K [A,B,A] ++ [A,B]
    let u := a++[A]++c
    let v := p++q
    let w := a++p++[A]++q++c
    let M := fiveMask a p [A] q c
    let N := fiveMask a x [A] ([A]++q) c
    let E := fourCuts a x [A] ([A]++q) c 0
    ValidMask u v w M ∧ rho M=3 ∧
    (∀ i : Fin 4, original (fourCuts a p [A] q c i)=w ∧
      Admissible (fourCuts a p [A] q c i) M ∧
      successor (fourCuts a p [A] q c i)=(if i.val<2 then v++u else u++v) ∧
      degree u v (successor (fourCuts a p [A] q c i))=((1 : Nat) : WithTop Nat)) ∧
    ValidMask u v w N ∧ rho N=3 ∧ original E=w ∧ Admissible E N ∧
    successor E=wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
      [A] ++ q ++ [B,A] ++ wordPower J [A,B,A] ∧
    R.readout () ⟨α,A,H,J,K,L⟩ B=((2 : Nat) : WithTop Nat) ∧
    (degree u v w=((3 : Nat) : WithTop Nat) →
      IsMinimumMask u v w M 3 ∧ IsMinimumMask u v w N 3)

def actual : Realization signature.{u} :=
  realize signature (fun _ p B =>
    let A := p.2.1
    let a := wordPower p.2.2.1 [A,B,A] ++ [A,B]
    let c := [B,A] ++ wordPower p.2.2.2.1 [A,B,A]
    let q := wordPower (p.2.2.2.2.2+1) [A,B,A]
    let x := wordPower p.2.2.2.2.1 [A,B,A] ++ [A,B]
    degree (a++[A]++c)
      (wordPower (p.2.2.2.2.1+1) [A,B,A]++q)
      (successor (fourCuts a x [A] ([A]++q) c 0))) (fun e => Empty.elim e)

private theorem rejected_law : ¬arena.{u}.Law rejected := by
  intro h
  have he := (h a b (by simp [a,b]) 0 0 0 0).2.2.2.2.2.2.2.2.1
  change (⊤ : WithTop Nat)=((2 : Nat) : WithTop Nat) at he
  simp at he

private theorem actual_dependence :
    actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ a ≠
      actual.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ b := by
  have h₁ := (inserted_degree a 5 [] [6] [5] (by simp) rfl rfl rfl).2
  have h₂ := (periodic_repair a b (by simp [a,b]) 0 0 0 0).2.2.2.2.2.2.2.2.1
  have e₁ : actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ a =
      ((1 : Nat) : WithTop Nat) := by
    simpa [actual,realize,fourCuts,successor,wordPower,gap,occupied,
      List.replicate_succ] using h₁
  have e₂ : actual.{u}.readout () ⟨ULift.{u} Bool,a,0,0,0,0⟩ b =
      ((2 : Nat) : WithTop Nat) := h₂
  rw [e₁,e₂]
  norm_num

def source_registration : Registration arena.{u}
    (type_of% (@periodic_repair.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@periodic_repair.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Bool,a,0,0,0,0⟩,a,b,actual_dependence⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@periodic_repair.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S1.Words.HughesPeriodicRepair.periodic_repair.__information_unit
  realizationName := `Reg.D5.S1.Words.HughesPeriodicRepair.Repair.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.HughesPeriodicRepair
    definition := none
    coordinates := #[0,1,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Repair

end
end Reg.D5.S1.Words.HughesPeriodicRepair
