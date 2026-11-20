import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
import Reg.Support.DependentFamily

/-! Source-bound audits of simultaneous zeros at chiral events and of zeros of odd maps from the
two-sphere to the plane. -/

namespace Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality

open _root_.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the first event function at the candidate event. -/
abbrev signature : Signature where
  Params := event → ℝ
  State _ := event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Both domains, both admissibility premises, chirality, and both zero equations remain. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ om ∈ ({allEvents, collisionEvents} : Set (Set event)), ∀ f₁ f₂,
    admissible om f₁ → admissible om f₂ →
      ∃ x ∈ om, chiral x ∧ R.readout () f₁ x = 0 ∧ f₂ x = 0

private theorem zero_admissible (om : Set event) : admissible om (fun _ => 0) := by
  refine ⟨continuousOn_const, ?_, ?_⟩
  · intro x hx lam hlam sigma tau
    rfl
  · intro x hx
    simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, _, _, hzero, _⟩ := h allEvents (by simp)
    (fun _ => 0) (fun _ => 0) (zero_admissible allEvents) (zero_admissible allEvents)
  change (1 : ℝ) = 0 at hzero
  exact one_ne_zero hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun x => x 0 0), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
    definition := some {
      owner := `D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
      name := `D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.claim
      path := #[] }
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! The value of the planar map at a point of the unit sphere, in `planar_odd_map_zero`. -/
namespace PlanarZero

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

/-- Retain the complete map, continuity and oddness telescope of `planar_odd_map_zero`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ f : EuclideanSpace ℝ (Fin 3) → ℂ,
    ContinuousOn f (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    (∀ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f (-v) = -f v) →
    ∃ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, r.readout () f v = 0

/-- The zero map is continuous and odd, but the constant reading one never vanishes. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, h1⟩ := h (fun _ => 0) continuousOn_const (fun _ _ => neg_zero.symm)
  exact one_ne_zero h1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨fun v => ((‖v‖ : ℝ) : ℂ), 0, EuclideanSpace.single 0 1, ?_⟩
  change ((‖(0 : EuclideanSpace ℝ (Fin 3))‖ : ℝ) : ℂ) ≠
    ((‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ : ℝ) : ℂ)
  simp [EuclideanSpace.single, PiLp.norm_single]

def source_registration : Registration arena (type_of% @planar_odd_map_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@planar_odd_map_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end PlanarZero

def planar_odd_map_zero_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@planar_odd_map_zero) (Realization PlanarZero.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.planar_odd_map_zero_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.PlanarZero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨PlanarZero.arena⟩
  objectArena := .source ⟨PlanarZero.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source PlanarZero.arena ⟨PlanarZero.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PlanarZero.signature (fun _ f v => f v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
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
#print _root_.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.result
#print _root_.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
