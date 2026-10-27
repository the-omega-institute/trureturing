import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteSimplicialJoin

/-! The actual barycentric observation, with its complete finite-complex parameters. -/
noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteConeCollapse

namespace Reg.D5.S3.Geometry.FiniteSimplicialJoin

universe u v

structure Parameters where
  V : Type u
  W : Type v
  decV : DecidableEq V
  decW : DecidableEq W
  finV : Fintype V
  finW : Fintype W
  M : PreAbstractSimplicialComplex V
  N : PreAbstractSimplicialComplex W

attribute [instance] Parameters.decV Parameters.decW Parameters.finV Parameters.finW

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Space p.M × Space p.N × unitInterval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.V ⊕ p.W) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p s => representative p.M p.N s) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v}, ∀ a b : signature.State p,
    R.readout () p a = R.readout () p b ↔
      (ordinaryJoinSetoid (Space p.M) (Space p.N)).Rel a b

private theorem bridge : (type_of% (@representative_eq_iff.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p a b
    exact h p.M p.N a b
  · intro h V W dv dw fv fw M N a b
    exact h ⟨V,W,dv,dw,fv,fw,M,N⟩ a b

private abbrev testParameters : Parameters.{u,v} :=
  ⟨ULift.{u} Unit, ULift.{v} Unit, inferInstance, inferInstance,
    inferInstance, inferInstance, ⊤, ⊤⟩

private def testPoint (T : Type*) [Fintype T] [DecidableEq T] [Unique T] :
    Space (⊤ : PreAbstractSimplicialComplex T) := by
  refine ⟨fun _ => 1, {default}, ?_, ?_⟩
  · exact Finset.singleton_nonempty _
  · rw [← faceSimplex_eq_convexHull]
    refine ⟨fun _ => zero_le_one, ?_, ?_⟩
    · simp
    · intro w hw
      exact (hw (by simp [Unique.eq_default w])).elim

private def leftState : signature.{u,v}.State testParameters :=
  (testPoint _, testPoint _, 0)

private def rightState : signature.{u,v}.State testParameters :=
  (testPoint _, testPoint _, 1)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := (h testParameters leftState rightState).mp rfl
  have ht := congrArg (fun t : unitInterval => (t : ℝ)) hh.1
  norm_num [leftState, rightState] at ht

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨testParameters, leftState, rightState, ?_⟩
  intro h
  have hc := congrFun h (Sum.inl (⟨()⟩ : ULift.{u} Unit))
  norm_num [actual, realize, representative, leftState, rightState, testPoint] at hc

def family : Registration arena.{u,v} (type_of% (@representative_eq_iff.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@representative_eq_iff.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@representative_eq_iff.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteSimplicialJoin.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteSimplicialJoin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => representative p.M p.N s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteSimplicialJoin
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"],
      stateBinder := 8,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","body","body",
        "fn","arg","arg"],
      stateBinder := 9,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Formula

structure Parameters extends FiniteSimplicialJoin.Parameters.{u,v} where
  nonemptyM : Nonempty (Space M)
  nonemptyN : Nonempty (Space N)

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Space p.M × Space p.N × unitInterval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.V ⊕ p.W) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p s =>
    (joinHomeomorph p.M p.N p.nonemptyM p.nonemptyN (Quotient.mk _ s)).val)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v}, ∀ s : signature.State p,
    R.readout () p s = representative p.M p.N s

private theorem bridge : (type_of% (@joinHomeomorph_apply.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p s
    exact h p.M p.N p.nonemptyM p.nonemptyN s.1 s.2.1 s.2.2
  · intro h V W dv dw fv fw M N hM hN x y t
    exact h ⟨⟨V,W,dv,dw,fv,fw,M,N⟩,hM,hN⟩ (x,y,t)

private def testParameters : Parameters.{u,v} :=
  ⟨FiniteSimplicialJoin.testParameters, ⟨testPoint _⟩, ⟨testPoint _⟩⟩

private def leftState : signature.{u,v}.State testParameters :=
  (testPoint _, testPoint _, 0)

private def rightState : signature.{u,v}.State testParameters :=
  (testPoint _, testPoint _, 1)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hc := congrFun (h testParameters leftState)
    (Sum.inl (⟨()⟩ : ULift.{u} Unit))
  norm_num [rejected, realize, representative, leftState, testPoint] at hc

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨testParameters, leftState, rightState, ?_⟩
  intro h
  have hc := congrFun h (Sum.inl (⟨()⟩ : ULift.{u} Unit))
  change (joinHomeomorph _ _ _ _ (Quotient.mk _ leftState)).val _ =
    (joinHomeomorph _ _ _ _ (Quotient.mk _ rightState)).val _ at hc
  rw [joinHomeomorph_apply, joinHomeomorph_apply] at hc
  norm_num [leftState, rightState, testPoint] at hc

def family : Registration arena.{u,v} (type_of% (@joinHomeomorph_apply.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@joinHomeomorph_apply.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@joinHomeomorph_apply.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteSimplicialJoin.Formula.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteSimplicialJoin.Formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s =>
    (joinHomeomorph p.M p.N p.nonemptyM p.nonemptyN (Quotient.mk _ s)).val)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteSimplicialJoin
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "body","body","body","fn","arg"],
      stateBinder := 10,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Formula

#print axioms registration
#print axioms Formula.registration
end Reg.D5.S3.Geometry.FiniteSimplicialJoin
