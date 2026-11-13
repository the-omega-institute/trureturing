import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion

/-! The full family of boundary quotient evaluations and its source reconstruction. -/

noncomputable section

open Set Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion

namespace Reg.D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion

universe u

abbrev signature : Signature where
  Params := Σ E : Type u, E → ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (_hB : Convex ℝ B) {a : E} (_ha : a ∈ interior B)
    (L : E →L[ℝ] ℝ) (_hL : L ≠ 0) {g : E → ℝ} (_hg : Continuous g)
    (_hvan : ∀ x ∈ frontier B, L (x - a) * g x = 0),
    ∀ x ∈ frontier B, R.readout () ⟨E, g⟩ x = 0

private theorem bridge : (type_of% (@whole_boundary_factor_delete.{u})) ↔
    arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let L : ULift.{u} ℝ →L[ℝ] ℝ := ContinuousLinearEquiv.ulift.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : ULift.{u} ℝ →L[ℝ] ℝ => f ⟨1⟩) hz
    change (1 : ℝ) = 0 at hh
    exact one_ne_zero hh
  have ha : (0 : ULift.{u} ℝ) ∈ interior (closedBall 0 1) := by
    rw [interior_closedBall 0 one_ne_zero]
    simp
  have hx : (⟨1⟩ : ULift.{u} ℝ) ∈ frontier (closedBall 0 1) := by
    rw [frontier_closedBall 0 one_ne_zero]
    norm_num [mem_sphere, dist_eq_norm]
  have hh := @h (ULift.{u} ℝ) inferInstance inferInstance (closedBall 0 1)
    (convex_closedBall (0 : ULift.{u} ℝ) 1) 0 ha L hL (fun _ => 0)
    continuous_const (by intro x hx; simp) ⟨1⟩ hx
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℝ, ULift.down⟩, ⟨0⟩, ⟨1⟩, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (type_of% (@whole_boundary_factor_delete.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@whole_boundary_factor_delete.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_boundary_factor_delete.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion.__information_unit
  realizationName := `Reg.D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
