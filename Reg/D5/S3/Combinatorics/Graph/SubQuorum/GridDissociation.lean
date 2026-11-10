import D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Finset (Fin p.1 × Fin p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (p : Σ _ : ℕ, ℕ), Finset (Fin p.1 × Fin p.2) → ℕ :=
  fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (p : Σ _ : ℕ, ℕ), Finset (Fin p.1 × Fin p.2) :=
  fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ p _ => formula p.1 p.2+1) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {m n : ℕ} (S : Finset (Fin m × Fin n)), IsKIndependent (graph m n) 2 S →
    r.readout () ⟨m,n⟩ S ≤ formula m n

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hi : IsKIndependent (graph 0 0) 2 (∅ : Finset (Fin 0 × Fin 0)) := by
    simp [IsKIndependent]
  have hh := h ∅ hi
  change formula 0 0+1 ≤ formula 0 0 at hh
  omega

abbrev SourceClaim : Prop := ∀ {m n : ℕ} (S : Finset (Fin m × Fin n)),
  IsKIndependent (graph m n) 2 S → S.card ≤ formula m n

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun S hS => selection_bound S hS,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,1⟩,∅,{(0,0)},?_⟩
    change (∅ : Finset (Fin 1 × Fin 1)).card ≠ ({(0,0)} : Finset (Fin 1 × Fin 1)).card
    simp

noncomputable def selectionBoundRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation.selection_bound)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation.selection_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
