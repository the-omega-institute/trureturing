import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod
import Reg.Support.SingleDependentReadout

/-! The support cardinality is the readout that enables the dimension argument. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q flip)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod
  (not_two_coordinate_period)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset (Q 9)) (fun _ => ℕ)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (U : Finset (Q 9)), r.readout () () U = 258 →
    ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3 →
    ∀ (i j : Fin 9), i ≠ j → ¬ ∀ x ∈ U, flip (flip x i) j ∈ U

private def actual : Realization signature :=
  realize signature (fun _ _ U => U.card) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 258) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let U : Finset (Q 9) := ∅
  have hdeg : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3 := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro x
    exact (Finset.notMem_empty _ x.property).elim
  have hperiod : ∀ x ∈ U, flip (flip x (0 : Fin 9)) (1 : Fin 9) ∈ U := by
    simp [U]
  exact law U rfl hdeg 0 1 (by decide) hperiod

def sourceEvidence : Registration arena (type_of% @not_two_coordinate_period) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨not_two_coordinate_period, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(), ∅, {fun _ : Fin 9 => false}, ?_⟩
    change (∅ : Finset (Q 9)).card ≠ ({fun _ : Fin 9 => false} : Finset (Q 9)).card
    simp

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@not_two_coordinate_period) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod.not_two_coordinate_period.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => U.card) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms not_two_coordinate_period
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TwoCoordinatePeriod
