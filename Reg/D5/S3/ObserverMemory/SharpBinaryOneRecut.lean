import D5.S3.ObserverMemory.SharpBinaryOneRecut
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

/-! Audit of the lawful recut on the actual boundary image. -/

namespace Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut
open _root_.D5.S3.ObserverMemory.SharpBinaryOneRecut
open _root_.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature where
  Params := Set (List Bool)
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Boundary
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature :=
  realize signature (fun _ C k => image C (k, 1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : Nat) (C : Set (List Bool)), (∀ w ∈ C, w.length = n) → C.Nonempty →
      ∀ k : Nat, 1 ≤ k → k ≤ n →
      (residualSet C k).Finite ∧ 0 < Nat.card (residualSet C k) ∧
      (∀ z ∈ R.readout () C k, recut z ∈ residualSet C k) ∧
      Bounds C k (Nat.card (residualSet C k)+1) ∧
      (FullBranching C k → Bounds C k (Nat.card (residualSet C k)))) ∧
    (∀ N : Nat, 1 ≤ N → Attains N false ∧ Attains N true)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let C : Set (List Bool) := {[false]}
  have hl : ∀ w ∈ C, w.length = 1 := by
    intro w hw; have he : w = [false] := hw; rw [he]; rfl
  have hc : C.Nonempty := ⟨[false],rfl⟩
  have he := (h.1 1 C hl hc 1 le_rfl le_rfl).2.2.1
    ((∅ : Set (List Bool)),[]) (by trivial)
  obtain ⟨v,_,⟨f,hf⟩,hr⟩ := he
  have hh : f ∈ recut ((∅ : Set (List Bool)),[]) := hr ▸ hf
  exact hh

private theorem dependence : ObservationalDependence signature actualReadout := by
  intro i
  let C : Set (List Bool) := {[false]}
  refine ⟨C,1,2,?_⟩
  intro he
  change image C (1,1) = image C (2,1) at he
  have hm : boundary C ([],[false]) ∈ image C (1,1) := by
    exact ⟨⟨([],[false]),rfl,⟨[],rfl⟩⟩,rfl⟩
  rw [he] at hm
  obtain ⟨s,_⟩ := hm
  obtain ⟨f,hf⟩ := s.property.2
  have hw : (s.val.1 ++ s.val.2) ++ f = [false] := hf
  have ht := congrArg Prod.fst s.property.1
  have hl := congrArg List.length hw
  simp only [publicType,List.length_append,List.length_singleton] at ht hl
  omega

def sourceRegistration : Registration arena (type_of% sharp_binary_one_recut) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨sharp_binary_one_recut,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.SharpBinaryOneRecut.sharp_binary_one_recut)
    (type_of% (realize signature (fun _ C k => image C (k, 1)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.sharp_binary_one_recut.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ C k => image C (k, 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.SharpBinaryOneRecut,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["fn","arg","body","body","body","body","body","body","body",
        "arg","arg","fn","arg","body","domain","fn","arg"],
      stateBinder := 4,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false}] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sourceRegistration

namespace Encoding
abbrev signature : Signature where
  Params := Nat
  State N := Option (Fin N)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature :=
  realize signature (fun _ _ i => word i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev lengthArena : Arena where
  signature := signature
  Law R := ∀ {N : Nat} (i : Option (Fin N)), (R.readout () N i).length = N
abbrev injectiveArena : Arena where
  signature := signature
  Law R := ∀ N : Nat, Function.Injective (R.readout () N)
private theorem rejected_length : ¬ lengthArena.Law rejected := by
  intro h
  have hh := @h 1 none
  simp [rejected,realize] at hh
private theorem rejected_injective : ¬ injectiveArena.Law rejected := by
  intro h
  have hh := h 1 (a₁ := none) (a₂ := some ⟨0,by omega⟩) rfl
  cases hh
private theorem dependence : ObservationalDependence signature actualReadout := by
  intro i
  refine ⟨1,none,some ⟨0,by omega⟩,?_⟩
  intro he
  have hh := word_injective 1 he
  cases hh

def lengthSource : Registration lengthArena (type_of% @word_length) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨@word_length,rejected,rejected_length⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_length⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def injectiveSource : Registration injectiveArena (type_of% word_injective) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨word_injective,rejected,rejected_injective⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_injective⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def lengthRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.SharpBinaryOneRecut.word_length)
    (type_of% (realize signature (fun _ _ i => word i) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.word_length.__information_unit
  realizationName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.Encoding.lengthSource
  realizationSource := none
  generated := false
  arena := .source ⟨lengthArena⟩
  objectArena := .source ⟨lengthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthArena ⟨lengthSource⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => word i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.SharpBinaryOneRecut
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def injectiveRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.SharpBinaryOneRecut.word_injective)
    (type_of% (realize signature (fun _ _ i => word i) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.word_injective.__information_unit
  realizationName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.Encoding.injectiveSource
  realizationSource := none
  generated := false
  arena := .source ⟨injectiveArena⟩
  objectArena := .source ⟨injectiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source injectiveArena ⟨injectiveSource⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => word i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.SharpBinaryOneRecut
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms lengthSource
#print axioms injectiveSource
end Encoding

namespace CoordinateCardinality
abbrev signature : Signature where
  Params := Nat
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature :=
  realize signature (fun _ N full => Nat.card (Spare N full)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : Nat) (full : Bool), R.readout () N full = N + if full then 0 else 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 true
  simp [rejected,realize] at hh
private theorem dependence : ObservationalDependence signature actualReadout := by
  intro i
  refine ⟨0,true,false,?_⟩
  change Nat.card (Spare 0 true) ≠ Nat.card (Spare 0 false)
  rw [spare_card,spare_card]
  decide

def source : Registration arena (type_of% spare_card) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨spare_card,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.SharpBinaryOneRecut.spare_card)
    (type_of% (realize signature (fun _ N full => Nat.card (Spare N full))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.spare_card.__information_unit
  realizationName := `Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut.CoordinateCardinality.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N full => Nat.card (Spare N full)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.SharpBinaryOneRecut
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
end CoordinateCardinality
end
end Reg.D5.S3.ObserverMemory.SharpBinaryOneRecut
