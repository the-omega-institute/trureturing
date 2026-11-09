import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
import Reg.Support.SingleDependentReadout

/-! Source registration for the weighted path-neighbor identity. -/

namespace Reg.D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination.PathNeighborSum

open _root_.D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The parameters retain the path length and vertex; states are the original weights. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
    (fun p => Fin (Sigma.fst p) → ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature
    (fun _ p f => ∑ k ∈ (pathGraph (Sigma.fst p)).neighborFinset (Sigma.snd p), f k)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Only the weighted neighbour sum is replaced; both dependent boundary terms remain. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (f : Fin n → ℕ) (j : Fin n),
    R.readout () ⟨n, j⟩ f =
      (if h : 0 < j.val then f ⟨j.val - 1, by omega⟩ else 0) +
      (if h : j.val + 1 < n then f ⟨j.val + 1, h⟩ else 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 1) (fun _ => 0) 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ k ∈ (pathGraph 2).neighborFinset 0, (0 : ℕ)) ≠
    ∑ k ∈ (pathGraph 2).neighborFinset 0, (1 : ℕ)
  rw [path_neighbor_sum (fun _ : Fin 2 => 0) 0,
    path_neighbor_sum (fun _ : Fin 2 => 1) 0]
  norm_num

def source_registration : Registration arena (type_of% @path_neighbor_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@path_neighbor_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@path_neighbor_sum) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
      "PathNeighborSum") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str `Reg.D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
      "PathNeighborSum") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p f => ∑ k ∈ (pathGraph (Sigma.fst p)).neighborFinset (Sigma.snd p), f k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination.PathNeighborSum
