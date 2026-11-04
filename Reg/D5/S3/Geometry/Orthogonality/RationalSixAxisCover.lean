import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Orthogonality.RationalSixAxisCover

/-! A whole-sphere source-family audit of the actual inner-product observation. -/

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Orthogonality.RationalSixAxisCover

namespace Reg.D5.S3.Geometry.Orthogonality.RationalSixAxisCover

abbrev signature : Signature where
  Params := Σ _ : Fin 6, UnitSphere
  State _ := UnitSphere
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p y => inner ℝ (p.2 : Space) (y : Space))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ i : Fin 6, IsOpen (color i)) ∧
    (∀ (i : Fin 6) (x : UnitSphere), x ∈ color i →
      ∀ (y : UnitSphere), y ∈ color i → R.readout () ⟨i, x⟩ y ≠ 0) ∧
    (⋃ i : Fin 6, color i) = Set.univ

private def pole : UnitSphere :=
  ⟨WithLp.toLp 2 ![1, 0, 0], by
    simp [EuclideanSpace.norm_eq,
      Fin.sum_univ_succ]⟩

private theorem pole_color : pole ∈ color 4 := by
  norm_num [color, pole, axis, PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := h.2.1 4 pole pole_color pole pole_color
  exact hn rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let south : UnitSphere := ⟨-(pole : Space), by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using
      (show ‖(pole : Space)‖ = 1 from by
        simpa only [Metric.mem_sphere, dist_zero_right] using pole.property)⟩
  refine ⟨⟨0, pole⟩, pole, south, ?_⟩
  change inner ℝ (pole : Space) (pole : Space) ≠
    inner ℝ (pole : Space) (-(pole : Space))
  have hp : ‖(pole : Space)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using pole.property
  norm_num [inner_neg_right, hp]

def family : Registration arena (type_of% (@rational_six_axis_open_cover)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rational_six_axis_open_cover, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_six_axis_open_cover) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Geometry.Orthogonality.RationalSixAxisCover.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Orthogonality.RationalSixAxisCover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p y => inner ℝ (p.2 : Space) (y : Space)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Orthogonality.RationalSixAxisCover
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Geometry.Orthogonality.RationalSixAxisCover
