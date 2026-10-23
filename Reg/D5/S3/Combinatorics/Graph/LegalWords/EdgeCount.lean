import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount

open scoped BigOperators Classical
open _root_.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open _root_.D5.S3.Combinatorics.Graph.LegalWordDegree
open _root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => (legalWordGraph n).edgeFinset.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () () n = (∑ b : Legal n, occupationCount b.val) ∧
    (∑ b : Legal n, occupationCount b.val) =
      ∑ k ∈ Finset.range ((n + 1) / 2 + 1), k * supportCount n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  have hz : (∑ b : Legal 0, occupationCount b.val) = 0 := by
    simp [occupationCount]
  change 1 = (∑ b : Legal 0, occupationCount b.val) at h0
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (legalWordGraph 0).edgeFinset.card ≠ (legalWordGraph 1).edgeFinset.card
  rw [(edge_count 0).1, (edge_count 1).1]
  decide

noncomputable def registration : Registration arena
    (∀ n : ℕ,
      (legalWordGraph n).edgeFinset.card = (∑ b : Legal n, occupationCount b.val) ∧
      (∑ b : Legal n, occupationCount b.val) =
        ∑ k ∈ Finset.range ((n + 1) / 2 + 1), k * supportCount n k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount.edge_count)
      (type_of% (realize signature (fun _ _ n => (legalWordGraph n).edgeFinset.card)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (legalWordGraph n).edgeFinset.card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
