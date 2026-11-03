import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteGraphIndependenceReduction

noncomputable section
open Set
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteCoordinateTruncation
open _root_.D5.S3.Geometry.FiniteGraphIndependenceReduction

namespace Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  G : SimpleGraph V
  a : V
  D : Finset V

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.V → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.V → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => transfer p.a p.D x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (G : SimpleGraph V) (a : V) (D : Finset V),
    (∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) →
    ∀ {x : V → ℝ}, Avoid G x → ∀ p q, G.Adj p q →
      (x p = 0 ∧ R.readout () ⟨V, fv, dv, G, a, D⟩ x p = 0) ∨
      (x q = 0 ∧ R.readout () ⟨V, fv, dv, G, a, D⟩ x q = 0)

private theorem bridge : (type_of% (@transfer_common_zero.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv G a D hd x hx p q hpq
    exact @h V fv dv G a D hd x hx p q hpq
  · intro h V fv dv G a D hd x hx p q hpq
    exact @h V fv dv G a D hd x hx p q hpq

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let G : SimpleGraph (ULift.{u} Bool) := ⊤
  have hh := @h (ULift.{u} Bool) inferInstance inferInstance G ⟨false⟩ ∅
    (by simp) (fun _ => 0) (by intro p q hpq; exact Or.inl rfl)
    ⟨false⟩ ⟨true⟩ (by simp [G])
  change ((0 : ℝ) = 0 ∧ (1 : ℝ) = 0) ∨ (0 = 0 ∧ (1 : ℝ) = 0) at hh
  norm_num at hh

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, ⊥, ⟨()⟩, ∅⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (⟨()⟩ : testParameters.{u}.V)
  norm_num [actual, realize, transfer, testParameters] at hh

def family : Registration arena.{u} (type_of% (@transfer_common_zero.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@transfer_common_zero.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@transfer_common_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => transfer p.a p.D x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphIndependenceReduction
    definition := none
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace Retraction

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  G : SimpleGraph V
  a : V
  D : Finset V
  retained : a ∉ D
  domination : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Ispace (p.G.induce {b | b ∉ p.D})
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Ispace (p.G.induce {b | b ∉ p.D})
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p y => retraction p.G p.a p.D p.retained p.domination
    (inclusion p.G p.D y)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ =>
    FiniteCoordinateTruncation.vertex _ ⟨p.a, p.retained⟩) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (G : SimpleGraph V) (a : V) (D : Finset V) (ha : a ∉ D)
    (hd : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    (y : Ispace (G.induce {b | b ∉ D})),
      R.readout () ⟨V, fv, dv, G, a, D, ha, hd⟩ y = y

private theorem bridge : (type_of% (@retraction_inclusion.{u})) ↔ arena.{u}.Law actual := by
  constructor <;> intro h V fv dv G a D ha hd y
  · exact @h V fv dv G a D ha hd y
  · exact @h V fv dv G a D ha hd y

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Bool, inferInstance, inferInstance, ⊥, ⟨false⟩, ∅, by simp, by simp⟩

private def first : signature.{u}.State testParameters :=
  FiniteCoordinateTruncation.vertex _ ⟨⟨false⟩, by simp⟩

private def second : signature.{u}.State testParameters :=
  FiniteCoordinateTruncation.vertex _ ⟨⟨true⟩, by simp⟩

private theorem first_ne_second : first.{u} ≠ second.{u} := by
  intro h
  have hh := congrArg (fun y => y.val ⟨⟨false⟩, by simp⟩) h
  norm_num [first, second, FiniteCoordinateTruncation.vertex, Pi.single_apply] at hh
  exact Bool.false_ne_true (congrArg ULift.down hh)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.finiteVertices testParameters.decidableVertices
    testParameters.G testParameters.a testParameters.D testParameters.retained
    testParameters.domination second
  exact first_ne_second hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, first, second, ?_⟩
  intro h
  change retraction _ _ _ _ _ (inclusion _ _ first) =
    retraction _ _ _ _ _ (inclusion _ _ second) at h
  rw [retraction_inclusion, retraction_inclusion] at h
  exact first_ne_second h

def family : Registration arena.{u} (type_of% (@retraction_inclusion.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@retraction_inclusion.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@retraction_inclusion.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction.Retraction.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction.Retraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y =>
    retraction p.G p.a p.D p.retained p.domination (inclusion p.G p.D y))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGraphIndependenceReduction
    definition := none
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Retraction
end Reg.D5.S3.Geometry.FiniteGraphIndependenceReduction
