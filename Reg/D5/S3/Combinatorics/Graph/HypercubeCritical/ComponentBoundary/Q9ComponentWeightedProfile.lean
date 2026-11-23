import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
import Reg.Support.SingleDependentReadout

/-! The observed squared norm sets the threshold for the weighted row. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile

open scoped BigOperators Matrix
open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary (directions)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
  (componentFinset mem_componentFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
  (componentDefect componentDefect_det_eq componentParityFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram (signed)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation (defect)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
  (exists_weighted_row_of_componentDefect_det_eq_zero)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 9 → ℝ) (fun _ => ℝ)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (w : Fin 9 → ℝ), (∀ i, 0 ≤ w i) → (componentDefect w U b C).det = 0 →
      ∃ x ∈ componentFinset U C,
        Real.sqrt (r.readout () () w) ≤ ∑ i ∈ directions (componentFinset U C) x, w i

private def actual : Realization signature :=
  realize signature (fun _ _ w => ∑ i, w i ^ 2) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let x : Q 9 := fun _ => false
  let U : Finset (Q 9) := {x}
  let y : (U : Set (Q 9)) := ⟨x, Finset.mem_singleton_self x⟩
  let C := ((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk y
  let b := parity x
  have hmem : x ∈ componentParityFinset U b C := by
    apply Finset.mem_filter.mpr
    exact ⟨(mem_componentFinset U C x).mpr ⟨y.property, rfl⟩, rfl⟩
  have hdet : (componentDefect (0 : Fin 9 → ℝ) U b C).det = 0 := by
    rw [componentDefect_det_eq]
    have hs : signed (0 : Fin 9 → ℝ) = 0 := by
      ext i j
      simp [signed]
    rw [hs]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨1, fun h => one_ne_zero (congrFun h ⟨x, hmem⟩), ?_⟩
    simp [defect]
  obtain ⟨z, _, hz⟩ := law U b C 0 (fun _ => le_rfl) hdet
  change Real.sqrt 1 ≤ ∑ i ∈ directions (componentFinset U C) z, (0 : ℝ) at hz
  norm_num at hz

def sourceEvidence : Registration arena
    (type_of% @exists_weighted_row_of_componentDefect_det_eq_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_weighted_row_of_componentDefect_det_eq_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    change (∑ _ : Fin 9, (0 : ℝ) ^ 2) ≠ ∑ _ : Fin 9, (1 : ℝ) ^ 2
    norm_num

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_weighted_row_of_componentDefect_det_eq_zero) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile.exists_weighted_row_of_componentDefect_det_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => ∑ i, w i ^ 2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
