import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.OccupiedFiberSubstitution

noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution
open _root_.D5.S3.Geometry.OccupiedFiberSubstitution

namespace Reg.D5.S3.Geometry.OccupiedFiberSubstitution
universe u w

namespace Adjacency

/-- All six parameter coordinates of the original seven-binder telescope. -/
structure Parameters where
  V : Type u
  D : V → Type w
  G : SimpleGraph V
  H : ∀ v, SimpleGraph (D v)
  T : Set (Sigma D)
  x : T

abbrev signature : Signature where
  Params := Parameters.{u,w}
  State p := p.T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,w} :=
  realize signature (fun _ p y =>
    (selectedGraph p.G p.H p.T).Adj (vertexEquiv p.T p.x) (vertexEquiv p.T y))
    (fun e => nomatch e)

def rejected : Realization signature.{u,w} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,w}
  Law R := ∀ p : Parameters.{u,w}, ∀ y : p.T,
    ((substitution p.G p.H).induce p.T).Adj p.x y ↔ R.readout () p y

private theorem bridge : (type_of% (@adjacency_iff.{u,w})) ↔ arena.{u,w}.Law actual := by
  constructor
  · intro h p y
    exact h p.G p.H p.T p.x y
  · intro h V D G H T x y
    exact h ⟨V, D, G, H, T, x⟩ y

private def testParameters : Parameters.{u,w} :=
  ⟨ULift.{u} Bool, fun _ => ULift.{w} Unit, ⊤, fun _ => ⊥, Set.univ,
    ⟨⟨⟨false⟩, ⟨()⟩⟩, trivial⟩⟩

private def testPoint (b : Bool) : testParameters.{u,w}.T :=
  ⟨⟨⟨b⟩, ⟨()⟩⟩, trivial⟩

private theorem positive :
    ((substitution testParameters.{u,w}.G testParameters.{u,w}.H).induce
      testParameters.{u,w}.T).Adj testParameters.{u,w}.x (testPoint true) := by
  apply Or.inl
  change (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩
  intro h
  cases congrArg ULift.down h

private theorem rejected_law : ¬ arena.{u,w}.Law rejected := by
  intro h
  exact (h testParameters (testPoint true)).mp positive

private theorem dependence : ObservationalDependence signature.{u,w} actual := by
  intro i
  refine ⟨testParameters, testPoint false, testPoint true, ?_⟩
  intro h
  have hp := (adjacency_iff testParameters.{u,w}.G testParameters.{u,w}.H
    testParameters.{u,w}.T testParameters.{u,w}.x (testPoint true)).mp positive
  have hn : ¬ (selectedGraph testParameters.{u,w}.G testParameters.{u,w}.H
      testParameters.{u,w}.T).Adj (vertexEquiv testParameters.{u,w}.T testParameters.{u,w}.x)
        (vertexEquiv testParameters.{u,w}.T (testPoint false)) := by
    exact fun hh => hh.ne rfl
  exact hn (h.symm ▸ hp)

def family : Registration arena.{u,w} (type_of% (@adjacency_iff.{u,w})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@adjacency_iff.{u,w}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjacency_iff.{u,w}) (Realization signature.{u,w}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Geometry.OccupiedFiberSubstitution.Adjacency.__information_unit
  realizationName := `Reg.D5.S3.Geometry.OccupiedFiberSubstitution.Adjacency.family
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
    (selectedGraph p.G p.H p.T).Adj (vertexEquiv p.T p.x) (vertexEquiv p.T y))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@SimpleGraph.{u})
  sourceSelection := some {
    owner := `D5.S3.Geometry.OccupiedFiberSubstitution
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Adjacency

namespace Faces

/-- The complete original telescope, with G as state and every dictionary retained. -/
structure Parameters where
  V : Type u
  D : V → Type w
  decidableBase : DecidableEq V
  decidableFibers : ∀ v, DecidableEq (D v)
  H : ∀ v, SimpleGraph (D v)
  T : Set (Sigma D)

attribute [instance] Parameters.decidableBase Parameters.decidableFibers
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev signature : Signature where
  Params := Parameters.{u,w}
  State p := SimpleGraph p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PreAbstractSimplicialComplex (Sigma (selectedFiber p.T))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,w} :=
  realize signature (fun _ p G =>
    ((independenceComplex ((substitution G p.H).induce p.T)).toPreAbstractSimplicialComplex).map
      (graphIso G p.H p.T).toEquiv.toEmbedding) (fun e => nomatch e)

def rejected : Realization signature.{u,w} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,w}
  Law R := ∀ p : Parameters.{u,w}, ∀ G : SimpleGraph p.V,
    R.readout () p G = (independenceComplex (selectedGraph G p.H p.T)).toPreAbstractSimplicialComplex

private theorem bridge :
    (type_of% (@mapped_independence_faces.{u,w})) ↔ arena.{u,w}.Law actual := by
  constructor
  · intro h p G
    exact h G p.H p.T
  · intro h V D dv dd G H T
    exact h ⟨V, D, dv, dd, H, T⟩ G

private def testParameters : Parameters.{u,w} :=
  ⟨ULift.{u} Bool, fun _ => ULift.{w} Unit, inferInstance, inferInstance,
    fun _ => ⊥, Set.univ⟩

private def testVertex (b : Bool) : Sigma (selectedFiber testParameters.{u,w}.T) :=
  vertexEquiv testParameters.T ⟨⟨⟨b⟩, ⟨()⟩⟩, trivial⟩

private theorem rejected_law : ¬ arena.{u,w}.Law rejected := by
  intro h
  have hs := (independenceComplex
    (selectedGraph (⊥ : SimpleGraph testParameters.{u,w}.V)
      testParameters.H testParameters.T)).singleton_mem (testVertex false)
  change ({testVertex false} : Finset _) ∈
    (independenceComplex (selectedGraph (⊥ : SimpleGraph testParameters.{u,w}.V)
      testParameters.H testParameters.T)).toPreAbstractSimplicialComplex at hs
  rw [← h testParameters ⊥] at hs
  exact hs

private theorem dependence : ObservationalDependence signature.{u,w} actual := by
  intro i
  refine ⟨testParameters, ⊥, ⊤, ?_⟩
  intro he
  change ((independenceComplex ((substitution (⊥ : SimpleGraph testParameters.{u,w}.V)
      testParameters.H).induce testParameters.T)).toPreAbstractSimplicialComplex).map _ =
    ((independenceComplex ((substitution (⊤ : SimpleGraph testParameters.{u,w}.V)
      testParameters.H).induce testParameters.T)).toPreAbstractSimplicialComplex).map _ at he
  rw [mapped_independence_faces, mapped_independence_faces] at he
  let s : Finset (Sigma (selectedFiber testParameters.{u,w}.T)) :=
    {testVertex false, testVertex true}
  have hb : s ∈ (independenceComplex
      (selectedGraph (⊥ : SimpleGraph testParameters.{u,w}.V)
        testParameters.H testParameters.T)).toPreAbstractSimplicialComplex := by
    refine ⟨by simp [s], ?_⟩
    intro x hx y hy hxy
    simp [selectedGraph, substitution, testParameters]
  have ht : s ∉ (independenceComplex
      (selectedGraph (⊤ : SimpleGraph testParameters.{u,w}.V)
        testParameters.H testParameters.T)).toPreAbstractSimplicialComplex := by
    intro hs
    apply hs.2 (by simp [s]) (by simp [s]) (show testVertex false ≠ testVertex true from ?_) ?_
    · intro h
      cases congrArg (fun q : Sigma (selectedFiber testParameters.{u,w}.T) => q.1.val.down) h
    · apply Or.inl
      change (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩
      intro h
      cases congrArg ULift.down h
  exact ht (he ▸ hb)

def family : Registration arena.{u,w} (type_of% (@mapped_independence_faces.{u,w})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@mapped_independence_faces.{u,w}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mapped_independence_faces.{u,w}) (Realization signature.{u,w}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Geometry.OccupiedFiberSubstitution.Faces.__information_unit
  realizationName := `Reg.D5.S3.Geometry.OccupiedFiberSubstitution.Faces.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G =>
    ((independenceComplex ((substitution G p.H).induce p.T)).toPreAbstractSimplicialComplex).map
      (graphIso G p.H p.T).toEquiv.toEmbedding) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@SimpleGraph.{u})
  sourceSelection := some {
    owner := `D5.S3.Geometry.OccupiedFiberSubstitution
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 6]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Faces

#print axioms Adjacency.registration
#print axioms Faces.registration
end Reg.D5.S3.Geometry.OccupiedFiberSubstitution
