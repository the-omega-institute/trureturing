import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the path neighbor count and its degree sum. -/

namespace Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
open _root_.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace NeighborCard

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun l => Fin (l + 1)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ l b => ((SimpleGraph.pathGraph (l + 1)).neighborFinset b).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (l : ℕ) (b : Fin (l + 1)),
    R.readout () l b =
      (if b.val < l then 1 else 0) + (if 0 < b.val then 1 else 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 0
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨2, 0, 1, ?_⟩
  change ((SimpleGraph.pathGraph (2 + 1)).neighborFinset (0 : Fin (2 + 1))).card ≠
    ((SimpleGraph.pathGraph (2 + 1)).neighborFinset (1 : Fin (2 + 1))).card
  rw [path_neighbor_card, path_neighbor_card]
  norm_num

def source_registration : Registration arena (type_of% @path_neighbor_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨path_neighbor_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@path_neighbor_card) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.NeighborCard.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.NeighborCard
    "source_registration"
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
    (fun _ l b => ((SimpleGraph.pathGraph (l + 1)).neighborFinset b).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end NeighborCard

namespace DegreeSum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature
    (fun _ _ l => ∑ b : Fin (l + 1), ((SimpleGraph.pathGraph (l + 1)).neighborFinset b).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ l : ℕ, R.readout () () l = 2 * l

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(), 0, 1, ?_⟩
  change (∑ b : Fin (0 + 1), ((SimpleGraph.pathGraph (0 + 1)).neighborFinset b).card) ≠
    ∑ b : Fin (1 + 1), ((SimpleGraph.pathGraph (1 + 1)).neighborFinset b).card
  rw [sum_path_neighbor_card, sum_path_neighbor_card]
  norm_num

def source_registration : Registration arena (type_of% @sum_path_neighbor_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_path_neighbor_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_path_neighbor_card) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.DegreeSum.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.DegreeSum
    "source_registration"
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
    (fun _ _ l => ∑ b : Fin (l + 1), ((SimpleGraph.pathGraph (l + 1)).neighborFinset b).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end DegreeSum
end
end Reg.D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
