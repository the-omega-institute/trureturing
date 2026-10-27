import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.EuclideanSphereJoin

noncomputable section
open Set
open scoped unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.EuclideanSphereJoin
open _root_.D5.S3.Geometry.FiniteSimplicialJoin

namespace Reg.D5.S3.Geometry.EuclideanSphereJoin

universe u v

structure Parameters where
  E : Type u
  F : Type v
  groupE : NormedAddCommGroup E
  spaceE : letI := groupE; NormedSpace ℝ E
  groupF : NormedAddCommGroup F
  spaceF : letI := groupF; NormedSpace ℝ F

attribute [instance] Parameters.groupE Parameters.spaceE Parameters.groupF Parameters.spaceF

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := UnitSphere p.E × UnitSphere p.F × I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.E × p.F
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ s => representative s) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v}, ∀ a b : signature.State p,
    R.readout () p a = R.readout () p b ↔
      (ordinaryJoinSetoid (UnitSphere p.E) (UnitSphere p.F)).r a b

private theorem bridge : (type_of% (@representative_eq_iff.{u,v})) ↔
    arena.{u,v}.Law actual := by
  constructor
  · intro h p a b
    exact h a b
  · intro h E F ge se gf sf a b
    exact h ⟨E,F,ge,se,gf,sf⟩ a b

private def testParameters : Parameters.{u,v} :=
  ⟨ULift.{u} ℝ, ULift.{v} ℝ, inferInstance, inferInstance, inferInstance, inferInstance⟩

private def leftPoint : UnitSphere testParameters.{u,v}.E :=
  ⟨⟨1⟩, by simp [UnitSphere, Metric.mem_sphere_zero_iff_norm]⟩

private def rightPoint : UnitSphere testParameters.{u,v}.F :=
  ⟨⟨1⟩, by simp [UnitSphere, Metric.mem_sphere_zero_iff_norm]⟩

private def leftState : signature.{u,v}.State testParameters := (leftPoint, rightPoint, 0)
private def rightState : signature.{u,v}.State testParameters := (leftPoint, rightPoint, 1)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := (h testParameters leftState rightState).mp rfl
  have ht := congrArg (fun t : I => (t : ℝ)) hh.1
  norm_num [leftState, rightState] at ht

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨testParameters, leftState, rightState, ?_⟩
  intro h
  have hh : representative leftState = representative rightState := h
  have ht := (representative_eq_iff _ _).mp hh
  have hc := congrArg (fun t : I => (t : ℝ)) ht.1
  norm_num [leftState, rightState] at hc

def family : Registration arena.{u,v} (type_of% (@representative_eq_iff.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@representative_eq_iff.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@representative_eq_iff.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.EuclideanSphereJoin.__information_unit
  realizationName := `Reg.D5.S3.Geometry.EuclideanSphereJoin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => representative s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.EuclideanSphereJoin
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body",
        "fn","arg","arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Endpoint

abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := StdSphere p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := StdSphere (p.1+p.2+1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p y => sphereJoinHomeomorph p.1 p.2
    (Quotient.mk _ (coordinatePoint p.1, y, (0 : I)))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : ℕ × ℕ, ∀ y : StdSphere p.2,
    R.readout () p y = coordinatePoint (p.1+p.2+1)

theorem bridge : (type_of% (@sphereJoinHomeomorph_coordinatePoint)) ↔ arena.Law actual := by
  constructor
  · intro h p y
    exact h p.1 p.2 y
  · intro h p q y
    exact h (p,q) y

/-- The faithful endpoint observation is constant on each original state fiber. -/
theorem no_observational_dependence : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy ((sphereJoinHomeomorph_coordinatePoint p.1 p.2 x).trans
    (sphereJoinHomeomorph_coordinatePoint p.1 p.2 y).symm)

end Endpoint

#print axioms registration
#print axioms Endpoint.no_observational_dependence

end Reg.D5.S3.Geometry.EuclideanSphereJoin
