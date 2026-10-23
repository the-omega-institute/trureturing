import D5.S3.ObserverMemory.StrictAnchoredBoundary
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ A : Type, Nat × Set (List A)
  State p := List p.1 × List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (List p.1) × List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature := realize signature
  (fun _ p s => boundary p.2.2 s) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Type} [Finite A] [Nonempty A]
    (n : Nat) (C : Set (List A)) (fixedLength : ∀ f ∈ C, f.length = n)
    (_nonempty : C.Nonempty) (k d : Nat) (hd : d ≤ k) (hk : k ≤ n),
    (∀ s a, actual C s →
      Option.map (fun r => (publicType r, R.readout () ⟨A,n,C⟩ r)) (step n C s a) =
        boundaryStep n (publicType s) (R.readout () ⟨A,n,C⟩ s) a) ∧
    (∀ s s', actual C s → actual C s' → publicType s = publicType s' →
      (legal n C s = legal n C s' ↔ R.readout () ⟨A,n,C⟩ s = R.readout () ⟨A,n,C⟩ s')) ∧
    Set.range (fun s : typedState C (k,d) => R.readout () ⟨A,n,C⟩ s.val) = {b | b.1 ∈ residualSet C (k-d) ∧ b.2 ∈ pref b.1 d} ∧
    (∃ inst : Fintype (residualSet C (k-d)), letI := inst;
      Nat.card (Set.range (fun s : typedState C (k,d) => R.readout () ⟨A,n,C⟩ s.val)) = ∑ S : residualSet C (k-d), Nat.card (pref S.val d)) ∧
    (∀ (X : Type) (a : List A × List A → X), Exact n C a →
      ∃! factor : Set.range (fun s : typedState C (k,d) => a s.val) → Set.range (fun s : typedState C (k,d) => R.readout () ⟨A,n,C⟩ s.val),
        (Set.rangeFactorization (fun s : typedState C (k,d) => R.readout () ⟨A,n,C⟩ s.val) =
          factor ∘ Set.rangeFactorization (fun s : typedState C (k,d) => a s.val)) ∧
        Function.Surjective factor ∧
        Nat.card (Set.range (fun s : typedState C (k,d) => R.readout () ⟨A,n,C⟩ s.val)) ≤ Nat.card (Set.range (fun s : typedState C (k,d) => a s.val)))

def rejected : Realization signature := realize signature
  (fun _ _ _ => (∅,[])) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let C : Set (List Bool) := {f | f.length = 1}
  have hf : ∀ f ∈ C, f.length = 1 := fun _ h => h
  have hn : C.Nonempty := ⟨[false],rfl⟩
  have hp := (h 1 C hf hn 1 1 le_rfl le_rfl).1
    ([],[false]) (.delete false) (by exact ⟨[],rfl⟩)
  simp [rejected,realize,step,publicType,boundaryStep] at hp

def sourceRegistration : Registration arena (arena.Law actualReadout) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨strict_anchored_specialization,rejected,rejected_law⟩
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
    refine ⟨⟨Bool,1,{f | f.length = 1}⟩,([],[false]),([],[true]),?_⟩
    intro h
    have ht := congrArg (fun b => b.2) h
    simp [actualReadout,realize,boundary] at ht

noncomputable def registration : LeanInformationAudit.Contract.Registration.{1,0,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.StrictAnchoredBoundary.strict_anchored_specialization)
    (type_of% (realize signature (fun _ p s => boundary p.2.2 s) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.StrictAnchoredBoundary.strict_anchored_specialization.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.StrictAnchoredBoundary.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p s => boundary p.2.2 s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sourceRegistration
end
end Reg.D5.S3.ObserverMemory.StrictAnchoredBoundary
