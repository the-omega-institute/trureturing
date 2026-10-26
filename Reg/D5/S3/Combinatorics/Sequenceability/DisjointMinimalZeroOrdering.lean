import D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
universe u v
abbrev signature : Signature where
  Params := Type u
  State α := Finset (Finset α)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ α Q => Set.PairwiseDisjoint (Q : Set (Finset α)) id) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {G : Type v} [AddCommGroup G]
    (f : α → G) (X C : Finset α)
    (hCX : C ⊆ X) (hz : (∑ x ∈ C, f x) = 0),
    ∃ Q : Finset (Finset α),
      (∀ B ∈ Q, B ⊆ X ∧ MinimalZeroSupport f B) ∧
      R.readout () α Q ∧ C = Q.biUnion id

private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u} := by
  intro h
  obtain ⟨Q, _, hQ, _⟩ := h (α := ULift.{u} Unit) (G := ULift.{v} ℤ)
    (fun _ => 0) ∅ ∅ (by simp) (by simp)
  exact hQ
private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let α := ULift.{u} Bool
  let a : α := ⟨false⟩
  let b : α := ⟨true⟩
  let A : Finset α := {a}
  let B : Finset α := {a, b}
  have hAB : A ≠ B := by
    intro h
    have hb : b ∈ A := h.symm ▸ (by simp [B])
    simpa [A, a, b] using hb
  refine ⟨α, ∅, {A, B}, ?_⟩
  intro he
  have hgood : actual.readout i α ∅ := by simp [actual, realize]
  rw [he] at hgood
  have hd : Disjoint A B := hgood (by simp) (by simp) hAB
  exact Finset.disjoint_left.mp hd (by simp [A]) (by simp [B])

def family : Registration arena.{u,v}
    (type_of% (@zero_decomposition_pairwise_disjoint.{u,v})) where
  actual := actual
  bridge := by rfl
  variation := ⟨@zero_decomposition_pairwise_disjoint.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zero_decomposition_pairwise_disjoint.{u,v}) (Realization signature.{u})
    (type_of% (@Finset.{u})) Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering.zero_decomposition_pairwise_disjoint.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Finset.{u})
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
