import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteGraphVertexSubstitution

/-! Coordinate recovery over all finite embedded complexes, including ghost vertices. -/
noncomputable section
open Set
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution
universe u x

structure Parameters where
  U : Type u
  X : Type x
  finiteSource : Fintype U
  decidableSource : DecidableEq U
  finiteTarget : Fintype X
  decidableTarget : DecidableEq X
  K : PreAbstractSimplicialComplex U
  f : U ↪ X

attribute [instance] Parameters.finiteSource Parameters.decidableSource
  Parameters.finiteTarget Parameters.decidableTarget

abbrev signature : Signature where
  Params := Parameters.{u,x}
  State p := Space (p.K.map p.f)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.X → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,x} :=
  realize signature (fun _ p y z => ∑ a, if p.f a = z then y.val (p.f a) else 0)
    (fun e => nomatch e)

def rejected : Realization signature.{u,x} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,x}
  Law R := ∀ p : Parameters.{u,x}, ∀ y : Space (p.K.map p.f), R.readout () p y = y.val

private theorem bridge :
    (type_of% (@mapped_coordinates.{u,x})) ↔ arena.{u,x}.Law actual := by
  constructor
  · intro h p y
    exact h p.K p.f y
  · intro h U X fu du fx dx K f y
    exact h ⟨U, X, fu, du, fx, dx, K, f⟩ y

private abbrev testParameters : Parameters.{u,x} :=
  ⟨ULift.{u} Bool, ULift.{x} Bool, inferInstance, inferInstance, inferInstance,
    inferInstance, ⊤, ⟨fun a => ⟨a.down⟩, fun _ _ h =>
      ULift.ext (congrArg (fun z : ULift.{x} Bool => z.down) h)⟩⟩

private def testPoint (b : Bool) : Space (testParameters.{u,x}.K.map testParameters.{u,x}.f) := by
  refine ⟨Pi.single (⟨b⟩ : testParameters.{u,x}.X) 1, ?_⟩
  refine ⟨{⟨b⟩}, ⟨{⟨b⟩}, Finset.singleton_nonempty _, ?_⟩, ?_⟩
  · simp only [Finset.image_singleton]
    rfl
  exact subset_convexHull ℝ _ ⟨⟨b⟩, by simp, rfl⟩

private theorem rejected_law : ¬ arena.{u,x}.Law rejected := by
  intro h
  have hh := congrFun (h testParameters.{u,x} (testPoint.{u,x} false)) (⟨false⟩ : testParameters.{u,x}.X)
  change (0 : ℝ) = 1 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u,x} actual := by
  intro i
  refine ⟨testParameters.{u,x}, testPoint.{u,x} false, testPoint.{u,x} true, ?_⟩
  intro h
  have h0 := mapped_coordinates testParameters.{u,x}.K testParameters.{u,x}.f (testPoint.{u,x} false)
  have h1 := mapped_coordinates testParameters.{u,x}.K testParameters.{u,x}.f (testPoint.{u,x} true)
  change (fun z => ∑ a, if testParameters.{u,x}.f a = z then
    (testPoint.{u,x} false).val (testParameters.{u,x}.f a) else 0) =
      (fun z => ∑ a, if testParameters.{u,x}.f a = z then
        (testPoint.{u,x} true).val (testParameters.{u,x}.f a) else 0) at h
  rw [h0, h1] at h
  have hh := congrFun h (⟨false⟩ : testParameters.{u,x}.X)
  have hne : (⟨false⟩ : ULift.{x} Bool) ≠ ⟨true⟩ := by
    intro he
    cases congrArg (fun z : ULift.{x} Bool => z.down) he
  change (Pi.single (⟨false⟩ : ULift.{x} Bool) (1 : ℝ) : ULift.{x} Bool → ℝ) ⟨false⟩ =
    (Pi.single (⟨true⟩ : ULift.{x} Bool) (1 : ℝ) : ULift.{x} Bool → ℝ) ⟨false⟩ at hh
  norm_num [Pi.single_apply, hne, Ne.symm hne] at hh

def family : Registration arena.{u,x} (type_of% (@mapped_coordinates.{u,x})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@mapped_coordinates.{u,x}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mapped_coordinates.{u,x}) (Realization signature.{u,x}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.family
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
    (fun _ p y z => ∑ a, if p.f a = z then y.val (p.f a) else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 8,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution
