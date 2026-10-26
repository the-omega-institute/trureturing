import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Riemannian.QuadraticGradientFlow
/-! Source-bound whole-family audits for actual Riemannian curves and their readouts. -/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal InnerProductSpace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Original172
open Original172.Example
noncomputable section
universe u v
local notation "IR" => 𝓘(ℝ, ℝ)
local notation "IP" => 𝓘(ℝ, Plane)
namespace Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow
namespace FlowDerivative
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Plane
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ => flow) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
∀ (t : ℝ),
    HasDerivAt (R.readout () ()) (point (-Real.exp (-t)) (-2*Real.exp (-2*t))) t

theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hd := (h 0).unique (hasDerivAt_const (0 : ℝ) (0 : Plane))
  have h0 := congrArg (fun p : Plane => p 0) hd
  norm_num [point] at h0

def evidence : Registration arena (type_of% (@Original172.Example.flow_hasDerivAt)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(@Original172.Example.flow_hasDerivAt), bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h0 := congrArg (fun p : Plane => p 0) h
    have he : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    simp [actual, realize, flow, point] at h0
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Original172.Example.flow_hasDerivAt) (type_of% (realize signature (fun _ _ => flow) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.FlowDerivative.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.FlowDerivative.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => flow) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Riemannian.QuadraticGradientFlow,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "fn", "arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end FlowDerivative

namespace StrictTriangle
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ a => ‖point (a^2) (a^4) - point 1 1‖) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ a => ‖point a (a^2) - point 1 1‖ + ‖point (a^2) (a^4) - point a (a^2)‖) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
∀ {a : ℝ} (ha : 0 < a) (ha1 : a < 1),
    R.readout () () a <
      ‖point a (a^2) - point 1 1‖ + ‖point (a^2) (a^4) - point a (a^2)‖

theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hbad := h (a := (1/2 : ℝ)) (by norm_num) (by norm_num)
  exact (lt_irrefl _) hbad

def evidence : Registration arena (type_of% (@Original172.Example.parabola_strict_triangle)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(@Original172.Example.parabola_strict_triangle), bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hp : point (0 : ℝ) 0 - point 1 1 ≠ 0 := by
      intro hz
      have h0 := congrArg (fun p : Plane => p 0) hz
      norm_num [point] at h0
    have hn := norm_pos_iff.mpr hp
    norm_num [actual, realize] at h
    exact (ne_of_gt hn) h

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Original172.Example.parabola_strict_triangle) (type_of% (realize signature (fun _ _ a => ‖point (a^2) (a^4) - point 1 1‖) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.StrictTriangle.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.StrictTriangle.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a => ‖point (a^2) (a^4) - point 1 1‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Riemannian.QuadraticGradientFlow,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end StrictTriangle

namespace StrictAction
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Plane
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ => flow) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ t => flow 0 + ((pathELength IP flow 0 t).toReal + 1) • point 1 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
∀ {T : ℝ} (hT : 0 < T),
    pathELength IP flow 0 T < ⊤ ∧
    (riemannianEDist IP (flow 0) (R.readout () () T)).toReal <
      (pathELength IP flow 0 T).toReal ∧
    (riemannianEDist IP (flow 0) (flow T))^2 /
      ((2:ℝ≥0∞)*ENNReal.ofReal T) < kineticAction (E := Plane) flow T

theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hs := (h (T := 1) (by norm_num)).2.1
  change (riemannianEDist IP (flow 0)
    (flow 0 + ((pathELength IP flow 0 1).toReal + 1) • point 1 0)).toReal <
      (pathELength IP flow 0 1).toReal at hs
  rw [← (IsRiemannianManifold.out (I := IP)), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, dist_eq_norm, norm_sub_rev,
    add_sub_cancel_left] at hs
  have hl : 0 ≤ (pathELength IP flow 0 1).toReal := ENNReal.toReal_nonneg
  have hp := PiLp.norm_apply_le
    (((pathELength IP flow 0 1).toReal + 1) • point 1 0) (0 : Fin 2)
  have hpos : 0 < (pathELength IP flow 0 1).toReal + 1 := by positivity
  have hbound : (pathELength IP flow 0 1).toReal + 1 ≤
      ‖((pathELength IP flow 0 1).toReal + 1) • point 1 0‖ := by
    simpa [point, Real.norm_eq_abs, abs_of_pos hpos] using hp
  linarith

def evidence : Registration arena (type_of% (@Original172.Example.S8_actual_strict_length_and_nonattainment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(@Original172.Example.S8_actual_strict_length_and_nonattainment), bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h0 := congrArg (fun p : Plane => p 0) h
    have he : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    simp [actual, realize, flow, point] at h0
    linarith

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Original172.Example.S8_actual_strict_length_and_nonattainment) (type_of% (realize signature (fun _ _ => flow) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.StrictAction.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow.StrictAction.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => flow) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Riemannian.QuadraticGradientFlow,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end StrictAction

end Reg.D5.S3.Geometry.Riemannian.QuadraticGradientFlow
