import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.BorsukUlam.PlanarOddMapZero
import Reg.Support.DependentFamily

/-! Source-bound audit of the zero of an odd map on the two-sphere. -/

namespace Reg.D5.S3.Topology.BorsukUlam.PlanarOddMapZero

open _root_.D5.S3.Topology.BorsukUlam.PlanarOddMapZero
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the given map at the candidate vector. -/
abbrev signature : Signature where
  Params := EuclideanSpace ℝ (Fin 3) → ℂ
  State _ := EuclideanSpace ℝ (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f v => f v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain continuity, oddness, sphere membership, and the zero equation. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
    ContinuousOn f (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    (∀ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f (-v) = -f v) →
    ∃ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, R.readout () f v = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, _, hzero⟩ := h (fun _ => 0) continuousOn_const (by intros; simp)
  change (1 : ℂ) = 0 at hzero
  exact one_ne_zero hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun v => (v 0 : ℂ)), 0, EuclideanSpace.single 0 1, ?_⟩
  simp [actual, realize, EuclideanSpace.single, PiLp.single_apply]

def source_registration : Registration arena (type_of% @planar_odd_map_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨planar_odd_map_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Topology.BorsukUlam.PlanarOddMapZero.planar_odd_map_zero)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.BorsukUlam.PlanarOddMapZero.unit
  realizationName := `Reg.D5.S3.Topology.BorsukUlam.PlanarOddMapZero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f v => f v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.BorsukUlam.PlanarOddMapZero
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Topology.BorsukUlam.PlanarOddMapZero.planar_odd_map_zero
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Topology.BorsukUlam.PlanarOddMapZero
