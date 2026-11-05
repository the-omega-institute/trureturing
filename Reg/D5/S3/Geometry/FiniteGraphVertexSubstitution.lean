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
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushAt
universe u x

structure Parameters where
  U : Type u
  X : Type x
  finiteSource : Fintype U
  decidableSource : DecidableEq U
  finiteTarget : Fintype X
  decidableTarget : DecidableEq X
  f : U ↪ X
  u : U

attribute [instance] Parameters.finiteSource Parameters.decidableSource
  Parameters.finiteTarget Parameters.decidableTarget

abbrev signature : Signature where
  Params := Parameters.{u,x}
  State p := p.U → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,x} :=
  realize signature (fun _ p v => push p.f v (p.f p.u)) (fun e => nomatch e)

def rejected : Realization signature.{u,x} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,x}
  Law R := ∀ {U : Type u} {X : Type x} [fu : Fintype U] [du : DecidableEq U]
    [fx : Fintype X] [dx : DecidableEq X] (f : U ↪ X) (v : U → ℝ) (a : U),
      R.readout () ⟨U, X, fu, du, fx, dx, f, a⟩ v = v a

private theorem bridge : (type_of% (@push_at.{u,x})) ↔ arena.{u,x}.Law actual := by
  constructor <;> intro h U X fu du fx dx f v a <;> exact @h U X fu du fx dx f v a

private theorem rejected_law : ¬ arena.{u,x}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) (ULift.{x} Unit) inferInstance inferInstance
    inferInstance inferInstance ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩
    (fun _ => 1) ⟨()⟩
  change (0 : ℝ) = 1 at hh
  norm_num at hh

private abbrev testParameters : Parameters.{u,x} :=
  ⟨ULift.{u} Unit, ULift.{x} Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩, ⟨()⟩⟩

private theorem dependence : ObservationalDependence signature.{u,x} actual := by
  intro i
  refine ⟨testParameters.{u,x}, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  change push testParameters.{u,x}.f (fun _ => 0) (testParameters.{u,x}.f testParameters.{u,x}.u) = push testParameters.{u,x}.f (fun _ => 1) (testParameters.{u,x}.f testParameters.{u,x}.u) at h
  norm_num [push, testParameters] at h

def family : Registration arena.{u,x} (type_of% (@push_at.{u,x})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@push_at.{u,x}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@push_at.{u,x}) (Realization signature.{u,x}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushAt.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushAt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => push p.f v (p.f p.u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushAt

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushOff
universe u x

structure Parameters where
  U : Type u
  X : Type x
  finiteSource : Fintype U
  decidableSource : DecidableEq U
  finiteTarget : Fintype X
  decidableTarget : DecidableEq X
  f : U ↪ X
  z : X

attribute [instance] Parameters.finiteSource Parameters.decidableSource
  Parameters.finiteTarget Parameters.decidableTarget

abbrev signature : Signature where
  Params := Parameters.{u,x}
  State p := p.U → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,x} :=
  realize signature (fun _ p v => push p.f v p.z) (fun e => nomatch e)

def rejected : Realization signature.{u,x} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,x}
  Law R := ∀ {U : Type u} {X : Type x} [fu : Fintype U] [du : DecidableEq U]
    [fx : Fintype X] [dx : DecidableEq X] (f : U ↪ X) (v : U → ℝ) (z : X) (hz : z ∉ Set.range f),
      R.readout () ⟨U, X, fu, du, fx, dx, f, z⟩ v = 0

private theorem bridge : (type_of% (@push_off.{u,x})) ↔ arena.{u,x}.Law actual := by
  constructor <;> intro h U X fu du fx dx f v z hz <;> exact @h U X fu du fx dx f v z hz

private theorem rejected_law : ¬ arena.{u,x}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Empty) (ULift.{x} Unit) inferInstance inferInstance
    inferInstance inferInstance ⟨(fun e => e.down.elim), (fun e => e.down.elim)⟩
    (fun _ => 0) ⟨()⟩ (by rintro ⟨e, _⟩; exact e.down.elim)
  change (1 : ℝ) = 0 at hh
  norm_num at hh

private abbrev testParameters : Parameters.{u,x} :=
  ⟨ULift.{u} Unit, ULift.{x} Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩, ⟨()⟩⟩

private theorem dependence : ObservationalDependence signature.{u,x} actual := by
  intro i
  refine ⟨testParameters.{u,x}, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  change push testParameters.{u,x}.f (fun _ => 0) testParameters.{u,x}.z = push testParameters.{u,x}.f (fun _ => 1) testParameters.{u,x}.z at h
  norm_num [push, testParameters] at h

def family : Registration arena.{u,x} (type_of% (@push_off.{u,x})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@push_off.{u,x}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@push_off.{u,x}) (Realization signature.{u,x}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushOff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushOff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => push p.f v p.z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.PushOff

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.SumPush
universe u x

structure Parameters where
  U : Type u
  X : Type x
  finiteSource : Fintype U
  decidableSource : DecidableEq U
  finiteTarget : Fintype X
  decidableTarget : DecidableEq X
  f : U ↪ X

attribute [instance] Parameters.finiteSource Parameters.decidableSource
  Parameters.finiteTarget Parameters.decidableTarget

abbrev signature : Signature where
  Params := Parameters.{u,x}
  State p := p.U → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,x} :=
  realize signature (fun _ p v => ∑ z, push p.f v z) (fun e => nomatch e)

def rejected : Realization signature.{u,x} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,x}
  Law R := ∀ {U : Type u} {X : Type x} [fu : Fintype U] [du : DecidableEq U]
    [fx : Fintype X] [dx : DecidableEq X] (f : U ↪ X) (v : U → ℝ) ,
      R.readout () ⟨U, X, fu, du, fx, dx, f⟩ v = ∑ a, v a

private theorem bridge : (type_of% (@sum_push.{u,x})) ↔ arena.{u,x}.Law actual := by
  constructor <;> intro h U X fu du fx dx f v  <;> exact @h U X fu du fx dx f v

private theorem rejected_law : ¬ arena.{u,x}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) (ULift.{x} Unit) inferInstance inferInstance
    inferInstance inferInstance ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩
    (fun _ => 0)
  change (1 : ℝ) = ∑ _ : ULift.{u} Unit, (0 : ℝ) at hh
  norm_num at hh

private abbrev testParameters : Parameters.{u,x} :=
  ⟨ULift.{u} Unit, ULift.{x} Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩⟩

private theorem dependence : ObservationalDependence signature.{u,x} actual := by
  intro i
  refine ⟨testParameters.{u,x}, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  change (∑ z, push testParameters.{u,x}.f (fun _ => 0) z) = (∑ z, push testParameters.{u,x}.f (fun _ => 1) z) at h
  rw [sum_push, sum_push] at h
  norm_num at h

def family : Registration arena.{u,x} (type_of% (@sum_push.{u,x})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@sum_push.{u,x}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_push.{u,x}) (Realization signature.{u,x}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.SumPush.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.SumPush.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => ∑ z, push p.f v z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.SumPush

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.Unrestricted
universe u

abbrev signature : Signature where
  Params := Type u
  State p := SimpleGraph p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PreAbstractSimplicialComplex p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ G => restricted G (fun _ => True)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {U : Type u} [du : DecidableEq U] (G : SimpleGraph U),
    R.readout () U G = (independenceComplex G).toPreAbstractSimplicialComplex

private theorem bridge : (type_of% (@unrestricted.{u})) ↔ arena.{u}.Law actual := by
  constructor <;> intro h U du G <;> exact @h U du G

private abbrev testParameters := ULift.{u} Bool

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance ⊥
  have hs : ({⟨()⟩} : Finset (ULift.{u} Unit)) ∈
      (independenceComplex (⊥ : SimpleGraph (ULift.{u} Unit))).toPreAbstractSimplicialComplex :=
    (independenceComplex _).singleton_mem _
  rw [← hh] at hs
  exact hs

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters.{u}, ⊥, ⊤, ?_⟩
  intro h
  change restricted (⊥ : SimpleGraph testParameters.{u}) (fun _ => True) =
    restricted (⊤ : SimpleGraph testParameters.{u}) (fun _ => True) at h
  have hs : ({⟨false⟩, ⟨true⟩} : Finset testParameters.{u}) ∈
      restricted (⊥ : SimpleGraph testParameters.{u}) (fun _ => True) := by
    refine ⟨Finset.insert_nonempty _ _, ?_, fun _ _ => trivial⟩
    intro a ha b hb hab
    simp
  rw [h] at hs
  have hbad := hs.2.1 (show (⟨false⟩ : testParameters.{u}) ∈
    ({⟨false⟩, ⟨true⟩} : Finset testParameters.{u}) by simp)
    (show (⟨true⟩ : testParameters.{u}) ∈
    ({⟨false⟩, ⟨true⟩} : Finset testParameters.{u}) by simp)
    (show (⟨false⟩ : testParameters.{u}) ≠ ⟨true⟩ by decide)
  exact hbad (by simp)

def family : Registration arena.{u} (type_of% (@unrestricted.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@unrestricted.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unrestricted.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.Unrestricted.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.Unrestricted.family
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
    (fun _ _ G => restricted G (fun _ => True)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.Unrestricted

namespace Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.RestrictedMap
universe u x

structure Parameters where
  U : Type u
  X : Type x
  decidableSource : DecidableEq U
  decidableTarget : DecidableEq X
  G : SimpleGraph U
  F : SimpleGraph X
  f : U ↪ X

attribute [instance] Parameters.decidableSource Parameters.decidableTarget

abbrev signature : Signature where
  Params := Parameters.{u,x}
  State p := p.U → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PreAbstractSimplicialComplex p.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,x} :=
  realize signature (fun _ p q => (restricted p.G q).map p.f) (fun e => nomatch e)

def rejected : Realization signature.{u,x} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,x}
  Law R := ∀ {U : Type u} {X : Type x} [du : DecidableEq U] [dx : DecidableEq X] (G : SimpleGraph U) (F : SimpleGraph X)
    (f : U ↪ X) (hf : ∀ a b, G.Adj a b ↔ F.Adj (f a) (f b)) (q : U → Prop),
    R.readout () ⟨U, X, du, dx, G, F, f⟩ q =
      restricted F (fun z => ∃ a, q a ∧ f a = z)

private theorem bridge : (type_of% (@restricted_map.{u,x})) ↔ arena.{u,x}.Law actual := by
  constructor <;> intro h U X du dx G F f hf q <;> exact @h U X du dx G F f hf q

private abbrev testParameters : Parameters.{u,x} :=
  ⟨ULift.{u} Unit, ULift.{x} Unit, inferInstance, inferInstance, ⊥, ⊥, ⟨fun _ => ⟨()⟩, fun a b _ => Subsingleton.elim a b⟩⟩

private theorem test_adj (a b : testParameters.{u,x}.U) :
    testParameters.{u,x}.G.Adj a b ↔ testParameters.{u,x}.F.Adj (testParameters.{u,x}.f a) (testParameters.{u,x}.f b) := by
  simp [testParameters]

private theorem rejected_law : ¬ arena.{u,x}.Law rejected := by
  intro h
  have hh := @h testParameters.{u,x}.U testParameters.{u,x}.X inferInstance inferInstance testParameters.{u,x}.G testParameters.{u,x}.F testParameters.{u,x}.f test_adj.{u,x} (fun _ => True)
  have hs : ({⟨()⟩} : Finset testParameters.{u,x}.X) ∈ restricted testParameters.{u,x}.F
      (fun z => ∃ a, True ∧ testParameters.{u,x}.f a = z) := by
    refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
    · intro a ha b hb hab
      simp [testParameters]
    · intro a ha
      have he : a = ⟨()⟩ := Finset.mem_singleton.mp ha
      subst a
      exact ⟨⟨()⟩, trivial, rfl⟩
  rw [← hh] at hs
  exact hs

private theorem dependence : ObservationalDependence signature.{u,x} actual := by
  intro i
  refine ⟨testParameters.{u,x}, (fun _ => True), (fun _ => False), ?_⟩
  intro h
  change (restricted testParameters.{u,x}.G (fun _ => True)).map testParameters.{u,x}.f =
    (restricted testParameters.{u,x}.G (fun _ => False)).map testParameters.{u,x}.f at h
  rw [restricted_map _ _ _ test_adj.{u,x}, restricted_map _ _ _ test_adj.{u,x}] at h
  have hs : ({⟨()⟩} : Finset testParameters.{u,x}.X) ∈ restricted testParameters.{u,x}.F
      (fun z => ∃ a, True ∧ testParameters.{u,x}.f a = z) := by
    refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
    · intro a ha b hb hab
      simp [testParameters]
    · intro a ha
      have he : a = ⟨()⟩ := Finset.mem_singleton.mp ha
      subst a
      exact ⟨⟨()⟩, trivial, rfl⟩
  rw [h] at hs
  obtain ⟨a, ha, _⟩ := hs.2.2 ⟨()⟩ (by simp)
  exact ha

def family : Registration arena.{u,x} (type_of% (@restricted_map.{u,x})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@restricted_map.{u,x}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@restricted_map.{u,x}) (Realization signature.{u,x}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.RestrictedMap.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.RestrictedMap.family
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
    (fun _ p q => (restricted p.G q).map p.f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphVertexSubstitution
    definition := none
    coordinates := #[0, 1, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
      "body", "body", "fn", "arg"],
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteGraphVertexSubstitution.RestrictedMap
