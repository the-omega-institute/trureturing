import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.MengerCertificates

/-! Source-bound support observation for finite set-form Menger. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.MengerCertificates

open LeanInformationAudit
open SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.MengerCertificates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V, Σ m : Nat,
  Σ _a : Fin m → V, Σ _b : Fin m → V, Fin m

def signature : Signature where
  Params := Parameters.{u}
  State p := p.2.1.Walk (p.2.2.2.1 p.2.2.2.2.2) (p.2.2.2.2.1 p.2.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (A B : Finset V),
    (∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) ∧
    (∀ Y : Finset V, Separates G A B Y →
      ∀ (m : Nat) (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A) → (∀ i, b i ∈ B) →
        (∀ i j, i ≠ j → ∀ x : V, @Membership.mem V (List V) inferInstance
          (R.readout () ⟨V, G, m, a, b, i⟩ (p i)) x → x ∉ (p j).support) → m ≤ Y.card)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e _ => Empty.elim e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let V : Type u := ULift.{u} Unit
  let v : V := ⟨()⟩
  have hsep : Separates (⊥ : SimpleGraph V) {v} {v} {v} := by
    intro a ha b hb p
    exact ⟨a, ha, p.start_mem_support⟩
  have hbad := (h (⊥ : SimpleGraph V) {v} {v}).2 {v} hsep 2
    (fun _ => v) (fun _ => v) (fun _ => Walk.nil)
    (by simp) (by simp) (by intro i j hij x hx; simp [rejected, realize] at hx)
  norm_num at hbad

def family : Registration arena.{u} (type_of% (@exists_separator_paths_and_weak_duality.{u})) where
  actual := realize signature (fun _ _ p => p.support) (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@exists_separator_paths_and_weak_duality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let V : Type u := ULift.{u} Bool
    let G : SimpleGraph V := completeGraph V
    let a : Fin 1 → V := fun _ => ⟨false⟩
    let p : G.Walk ⟨false⟩ ⟨false⟩ := Walk.nil
    let q : G.Walk ⟨false⟩ ⟨false⟩ :=
      Walk.cons (show G.Adj ⟨false⟩ ⟨true⟩ from by
        change (⟨false⟩ : V) ≠ ⟨true⟩
        intro h
        cases congrArg ULift.down h)
        (Walk.cons (show G.Adj ⟨true⟩ ⟨false⟩ from by
          change (⟨true⟩ : V) ≠ ⟨false⟩
          intro h
          cases congrArg ULift.down h) Walk.nil)
    refine ⟨⟨V, G, 1, a, a, 0⟩, p, q, ?_⟩
    change p.support ≠ q.support
    intro h
    have hl := congrArg List.length h
    norm_num [p, q] at hl

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_separator_paths_and_weak_duality.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.MengerCertificates.exists_separator_paths_and_weak_duality.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MengerCertificates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.support) (fun e _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MengerCertificates
    definition := none
    coordinates := #[0, 2, 7, 8, 9, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body",
        "body", "body", "body", "body", "body", "domain", "body", "body", "body", "body",
        "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.Walks.MengerCertificates
