import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct
import Reg.Support.SingleDependentReadout

/-! The squared weight norm is the lower bound for the product of the two caps. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct

open scoped BigOperators Matrix
open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary (directions)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents (mem_componentFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
  (componentDefect componentDefect_det_eq componentParityFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram (signed)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation (defect)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct
  (sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 9 → ℝ) (fun _ => ℝ)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law f := ∀ (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (w : Fin 9 → ℝ), (∀ i, 0 ≤ w i) → ∀ (r s : ℝ), 0 ≤ r → 0 ≤ s →
      (∀ x ∈ componentParityFinset U b C,
        ∑ i ∈ directions (componentParityFinset U (!b) C) x, w i ≤ r) →
      (∀ y ∈ componentParityFinset U (!b) C,
        ∑ i ∈ directions (componentParityFinset U b C) y, w i ≤ s) →
      (componentDefect w U b C).det = 0 → f.readout () () w ≤ r * s

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
  have hmem : x ∈ componentParityFinset U b C :=
    Finset.mem_filter.mpr ⟨(mem_componentFinset U C x).mpr ⟨y.property, rfl⟩, rfl⟩
  have hdet : (componentDefect (0 : Fin 9 → ℝ) U b C).det = 0 := by
    rw [componentDefect_det_eq]
    have hzero : signed (0 : Fin 9 → ℝ) = 0 := by
      ext i j
      simp [signed]
    rw [hzero]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨1, fun h => one_ne_zero (congrFun h ⟨x, hmem⟩), ?_⟩
    simp [defect]
  have h := law U b C 0 (fun _ => le_rfl) 0 0 le_rfl le_rfl
    (by intros; simp) (by intros; simp) hdet
  change (1 : ℝ) ≤ 0 * 0 at h
  norm_num at h

def sourceEvidence : Registration arena
    (type_of% @sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    change (∑ _ : Fin 9, (0 : ℝ) ^ 2) ≠ ∑ _ : Fin 9, (1 : ℝ) ^ 2
    norm_num

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct.sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct.sourceEvidence
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
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceEvidence
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedParityProduct
