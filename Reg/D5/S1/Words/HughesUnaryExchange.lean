import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.HughesUnaryExchange
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.HughesUnaryExchange

open _root_.D5.S1.Words.HughesBlockExchange
open _root_.D5.S1.Words.UnaryGapWords
open _root_.D5.S1.Words.HughesUnaryInsertion
open _root_.D5.S1.Words.HughesUnaryExchange
open _root_.D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : List α, List α
  State p := BlockCut p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := WithTop Nat
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (u v : List α) (E : BlockCut α) (M : List Side) (r : Nat),
    u ≠ [] → v ≠ [] → IsMinimumMask u v (original E) M r → 1 < r → Admissible E M →
    ((∃ a m, 0 < m ∧ u = List.replicate m a) ∨
      (∃ a n, 0 < n ∧ v = List.replicate n a)) →
    R.readout () ⟨α,u,v⟩ E = ((r-1 : Nat) : WithTop Nat)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => Empty.elim e)

private def a : ULift.{u} Bool := ⟨false⟩
private def b : ULift.{u} Bool := ⟨true⟩
private def su : List (ULift.{u} Bool) := [a,a]
private def sv : List (ULift.{u} Bool) := [b]
private def cut : BlockCut (ULift.{u} Bool) := ⟨[],[a],[b],[a]⟩
private def mask : List Side := [.first,.second,.first]

private theorem sample_min : IsMinimumMask su.{u} sv (original cut) mask 2 := by
  have h := (inserted_degree a 2 [b] [0,0] [1,1]
    (by simp [a,b]) rfl rfl rfl).1
  simpa [su,sv,cut,mask,original,gap,grouped,occupied] using h

private theorem sample_admissible : Admissible cut.{u} mask := by
  refine ⟨by decide,by decide,⟨[],[.first],[.second],[.first]⟩,?_,rfl,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · decide
  · exact Or.inl ⟨rfl,rfl,rfl⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (α := ULift.{u} Bool) su sv cut mask 2 (by decide) (by decide)
    sample_min (by omega) sample_admissible (Or.inl ⟨a,2,by omega,rfl⟩)
  change (⊤ : WithTop Nat) = ((2-1 : Nat) : WithTop Nat) at he
  simp at he

private def depU : List (ULift.{u} Bool) := [a,a,a]
private def depV : List (ULift.{u} Bool) := [b,b]
private def cutTwo : BlockCut (ULift.{u} Bool) := ⟨[],[a],[b,b],[a,a]⟩
private def cutThree : BlockCut (ULift.{u} Bool) := ⟨[],[a],[b],[a,b,a]⟩
private def maskTwo : List Side := [.first,.second,.second,.first,.first]
private def maskThree : List Side := [.first,.second,.first,.second,.first]

private theorem min_two : IsMinimumMask depU.{u} depV (original cutTwo) maskTwo 2 := by
  have h := (inserted_degree a 3 [b,b] [0,0,0] [1,0,2]
    (by simp [a,b]) rfl rfl rfl).1
  simpa [depU,depV,cutTwo,maskTwo,original,gap,grouped,occupied] using h

private theorem min_three :
    IsMinimumMask depU.{u} depV (original cutThree) maskThree 3 := by
  have h := (inserted_degree a 3 [b,b] [0,0,0] [1,1,1]
    (by simp [a,b]) rfl rfl rfl).1
  simpa [depU,depV,cutThree,maskThree,original,gap,grouped,occupied] using h

private theorem admissible_two : Admissible cutTwo.{u} maskTwo := by
  refine ⟨by decide,by decide,⟨[],[.first],[.second,.second],[.first,.first]⟩,
    ?_,rfl,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · decide
  · exact Or.inl ⟨rfl,rfl,rfl⟩

private theorem admissible_three : Admissible cutThree.{u} maskThree := by
  refine ⟨by decide,by decide,⟨[],[.first],[.second],[.first,.second,.first]⟩,
    ?_,rfl,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · decide
  · exact Or.inl ⟨rfl,rfl,rfl⟩

private theorem valid_dependence :
    degree depU.{u} depV (successor cutTwo) ≠
      degree depU depV (successor cutThree) := by
  have h₂ := _root_.D5.S1.Words.HughesUnaryExchange.result depU depV cutTwo maskTwo 2
    (by simp [depU]) (by simp [depV]) min_two (by omega) admissible_two
    (Or.inl ⟨a,3,by omega,rfl⟩)
  have h₃ := _root_.D5.S1.Words.HughesUnaryExchange.result depU depV cutThree maskThree 3
    (by simp [depU]) (by simp [depV]) min_three (by omega) admissible_three
    (Or.inl ⟨a,3,by omega,rfl⟩)
  rw [h₂,h₃]
  norm_num

def source_registration : Registration arena.{u} (type_of% (@_root_.D5.S1.Words.HughesUnaryExchange.result.{u})) where
  actual := realize signature.{u}
    (fun _ p E => degree p.2.1 p.2.2 (successor E)) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.HughesUnaryExchange.result.{u},rejected,rejected_law⟩
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
    exact ⟨⟨ULift.{u} Bool,depU,depV⟩,cutTwo,cutThree,valid_dependence⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.HughesUnaryExchange.result.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S1.Words.HughesUnaryExchange.result.__information_unit
  realizationName := `Reg.D5.S1.Words.HughesUnaryExchange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p E => degree p.2.1 p.2.2 (successor E)) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.HughesUnaryExchange
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end
end Reg.D5.S1.Words.HughesUnaryExchange
