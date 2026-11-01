import D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

/-! The source family keeps every alphabet, language, lawful cut and attaining width. -/

namespace Reg.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
open _root_.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
open _root_.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature where
  Params := Σ A : Type, Set (List A)
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (Set (List p.1) × p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature :=
  realize signature (fun _ p k => oneBoundary p.2 k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Type) [Finite A], 2 ≤ Nat.card A →
    (∀ (n : Nat) (C : Set (List A)), (∀ w ∈ C, w.length = n) → C.Nonempty →
      ∀ k : Nat, 1 ≤ k → k ≤ n →
      FiniteCarriers C k ∧ 0 < Nat.card (residualSet C k) ∧
      StrictIdentification C k ∧
      (∀ z ∈ R.readout () ⟨A,C⟩ k, forward z ∈ residualSet C k) ∧
      Bounds C k (Nat.card (residualSet C k)+1) ∧
      (FullBranching C k → FullBounds C k)) ∧
    (∀ N : Nat, 1 ≤ N → Attains (A := A) N false ∧ Attains (A := A) N true)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let C : Set (List Bool) := {[false]}
  have hl : ∀ w ∈ C, w.length = 1 := by
    intro w hw
    have he : w = [false] := hw
    rw [he]; rfl
  have hc : C.Nonempty := ⟨[false],rfl⟩
  have he := ((h Bool (by simp [Nat.card_eq_fintype_card])).1 1 C hl hc 1 le_rfl le_rfl).2.2.2.1
    ((∅ : Set (List Bool)),false) (by trivial)
  obtain ⟨v,_,⟨f,hf⟩,hr⟩ := he
  have hh : f ∈ forward ((∅ : Set (List Bool)),false) := hr ▸ hf
  exact hh

private theorem dependence : ObservationalDependence signature actualReadout := by
  intro i
  let C : Set (List Bool) := {[false,false]}
  refine ⟨⟨Bool,C⟩,1,2,?_⟩
  intro he
  change oneBoundary C 1 = oneBoundary C 2 at he
  have hm : (residual C [],false) ∈ oneBoundary C 1 := by
    refine ⟨⟨[],rfl,⟨[false,false],rfl⟩,rfl⟩,⟨[false],?_⟩⟩
    exact rfl
  rw [he] at hm
  obtain ⟨v,hv,_,hr⟩ := hm.1
  have hw : v ++ [false,false] = [false,false] := by
    change [false,false] ∈ residual C v
    rw [hr]
    exact rfl
  have hh := congrArg List.length hw
  simp only [List.length_append,List.length_cons,List.length_nil] at hh
  omega

def sourceRegistration : Registration arena (type_of% sharp_finite_alphabet_one_recut) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨sharp_finite_alphabet_one_recut,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{1,0,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut.sharp_finite_alphabet_one_recut)
    (type_of% (realize signature (fun _ p k => oneBoundary p.2 k) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut.sharp_finite_alphabet_one_recut.__information_unit
  realizationName := `Reg.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => oneBoundary p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
    definition := none
    coordinates := #[0,4]
    readouts := #[{
      path := #["body","body","body","fn","arg","body","body","body","body",
        "body","body","body","arg","arg","arg","fn","arg","body","domain","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
