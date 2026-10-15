import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.FourVertexRank
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.FourVertexRank
open _root_.D5.S3.Combinatorics.Graph.Walks.FourVertexRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical
noncomputable section
namespace Matching
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := SimpleGraph (Fin 4)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ H => pmCount H) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ H : SimpleGraph (Fin 4),
    (∀ M : H.Subgraph, M.IsPerfectMatching ↔
      ∃ j : Fin 3, (∀ i, H.Adj i (mate j i)) ∧
        ∀ i k, M.Adj i k ↔ mate j i = k) ∧
    R.readout () () H =
    (if H.Adj 0 1 ∧ H.Adj 2 3 then 1 else 0) +
    (if H.Adj 0 2 ∧ H.Adj 1 3 then 1 else 0) +
    (if H.Adj 0 3 ∧ H.Adj 1 2 then 1 else 0)

def registration : Registration arena
    (∀ H : SimpleGraph (Fin 4),
      (∀ M : H.Subgraph, M.IsPerfectMatching ↔
        ∃ j : Fin 3, (∀ i, H.Adj i (mate j i)) ∧
          ∀ i k, M.Adj i k ↔ mate j i = k) ∧
      pmCount H =
      (if H.Adj 0 1 ∧ H.Adj 2 3 then 1 else 0) +
      (if H.Adj 0 2 ∧ H.Adj 1 3 then 1 else 0) +
      (if H.Adj 0 3 ∧ H.Adj 1 2 then 1 else 0)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_matching_count, rejected, by
    intro h
    have hh := (h ⊥).2
    simp [rejected, realize] at hh⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · intro h
        have hh := (h ⊥).2
        simp [rejected, realize] at hh
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ⊥, ⊤, ?_⟩
    change pmCount ⊥ ≠ pmCount ⊤
    rw [(actual_matching_count ⊥).2, (actual_matching_count ⊤).2]
    simp

def registration_contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.Walks.FourVertexRank.actual_matching_count)
    (type_of% (realize signature (fun _ _ H => pmCount H) (fun e => nomatch e)))
    (Type) Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Walks.FourVertexRank.actual_matching_count "Reg.D5.S3.Combinatorics.Graph.Walks.FourVertexRank/Reg.D5.S3.Combinatorics.Graph.Walks.FourVertexRank.Matching.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.FourVertexRank.Matching.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ H => pmCount H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Graph.Walks.FourVertexRank
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_contract
end Matching
end
end Reg.D5.S3.Combinatorics.Graph.Walks.FourVertexRank
