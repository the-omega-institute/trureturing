import D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
open _root_.D5.S3.Combinatorics.Graph.SubQuorum.GridDissociation
open _root_.D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary

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

def bad : Realization signature := realize signature (fun _ _ _ => 2) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (S : Finset (Fin m × Fin n)), IsMinimalStarForming (graph m n) 2 S →
    7*r.readout () ⟨m,n⟩ S+(isolates (graph m n) S).card ≤ 4*(m*n)+2*m+2*n

private theorem singleton_minimal : IsMinimalStarForming (graph 1 1) 2 {(0,0)} := by
  constructor
  · intro v hv
    have he : v=(0,0) := Subsingleton.elim _ _
    exact (hv (by simp [he])).elim
  · intro T hT hf
    have he : T=∅ := Finset.eq_empty_of_ssubset_singleton hT
    have hh := (starForming_two_iff _ _).mp hf (0,0) (by simp [he])
    simp [he] at hh

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m:=1) (n:=1) (by omega) (by omega) {(0,0)} singleton_minimal
  change 7*2+(isolates (graph 1 1) {(0,0)}).card ≤ 4*(1*1)+2*1+2*1 at hh
  omega

abbrev SourceClaim : Prop := ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (S : Finset (Fin m × Fin n)), IsMinimalStarForming (graph m n) 2 S →
    7*S.card+(isolates (graph m n) S).card ≤ 4*(m*n)+2*m+2*n

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun hm hn S hS => forming_perimeter_bound hm hn S hS,bad,bad_law⟩
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

noncomputable def formingPerimeterBoundRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary.forming_perimeter_bound)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary.forming_perimeter_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary.family
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
    owner := `D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.SubQuorum.GridBoundary
