import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteForestIndependence

/-! Native realization-set readouts for the full forest and isolated-vertex statements. -/
noncomputable section
open Set ContinuousMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteForestIndependence

namespace Reg.D5.S3.Geometry.FiniteForestIndependence
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := SimpleGraph p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (p.V → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeSet (p : Parameters.{u}) (G : SimpleGraph p.V) : Set (p.V → ℝ) :=
  FiniteConeCollapse.realization
    (FiniteGraphVertexSubstitution.independenceComplex G).toPreAbstractSimplicialComplex

def actual : Realization signature.{u} :=
  realize signature (fun _ p G => nativeSet p G) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Bool, inferInstance, inferInstance⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, ⊥, ⊤, ?_⟩
  intro h
  let x : testParameters.{u}.V → ℝ := fun _ => 1 / 2
  have hm : x ∈ nativeSet testParameters (⊥ : SimpleGraph testParameters.V) := by
    apply (FiniteCoordinateTruncation.realization_iff _ _).mpr
    constructor
    · constructor
      · intro a; norm_num [x]
      · have hn : Fintype.card testParameters.{u}.V = 2 := rfl
        norm_num [x, hn]
    · simp [FiniteCoordinateTruncation.Avoid]
  change nativeSet testParameters (⊥ : SimpleGraph testParameters.V) =
    nativeSet testParameters (⊤ : SimpleGraph testParameters.V) at h
  rw [h] at hm
  have hz := ((FiniteCoordinateTruncation.realization_iff _ _).mp hm).2
    (⟨false⟩ : testParameters.V) (⟨true⟩ : testParameters.V) (by simp)
  norm_num [x] at hz

private abbrev singletonParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance⟩

private theorem empty_not_contractible (p : Parameters.{u}) :
    ¬ ContractibleSpace (↥(∅ : Set (p.V → ℝ))) := by
  intro hc
  let := hc
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (↥(∅ : Set (p.V → ℝ)))
  exact (e.invFun ()).property

abbrev classificationArena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ G : SimpleGraph p.V, G.IsAcyclic →
    IsEmpty p.V ∨ ContractibleSpace (↥(R.readout () p G)) ∨
      ∃ n : ℕ, Nonempty (↥(R.readout () p G) ≃ₕ EuclideanSphereJoin.StdSphere n)

private theorem classification_bridge : (type_of% (@classification.{u})) ↔
    classificationArena.{u}.Law actual := by
  constructor
  · intro h p G hG
    exact @h p.V p.finiteVertices p.decidableVertices G hG
  · intro h V fv dv G hG
    exact h ⟨V, fv, dv⟩ G hG

private theorem classification_rejected : ¬ classificationArena.{u}.Law rejected := by
  intro h
  have hh := h singletonParameters (⊥ : SimpleGraph singletonParameters.V)
    SimpleGraph.isAcyclic_bot
  rcases hh with he | hc | ⟨n, ⟨e⟩⟩
  · exact he.false ⟨()⟩
  · exact empty_not_contractible singletonParameters hc
  · exact (e.invFun (EuclideanSphereJoin.coordinatePoint n)).property

def classificationFamily : Registration classificationArena.{u}
    (type_of% (@classification.{u})) where
  actual := actual
  bridge := classification_bridge
  variation := ⟨classification_bridge.mp (@classification.{u}), rejected,
    classification_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, classification_rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def classificationRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classification.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteForestIndependence.classificationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteForestIndependence.classificationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classificationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G => nativeSet p G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev isolatedArena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ (G : SimpleGraph p.V) (a : p.V),
    (∀ w, ¬ G.Adj a w) → ContractibleSpace (↥(R.readout () p G))

private theorem isolated_bridge : (type_of% (@isolated_contractible.{u})) ↔
    isolatedArena.{u}.Law actual := by
  constructor
  · intro h p G a ha
    exact @h p.V p.finiteVertices p.decidableVertices G a ha
  · intro h V fv dv G a ha
    exact h ⟨V, fv, dv⟩ G a ha

private theorem isolated_rejected : ¬ isolatedArena.{u}.Law rejected := by
  intro h
  exact empty_not_contractible singletonParameters
    (h singletonParameters ⊥ ⟨()⟩ (by simp))

def isolatedFamily : Registration isolatedArena.{u} (type_of% (@isolated_contractible.{u})) where
  actual := actual
  bridge := isolated_bridge
  variation := ⟨isolated_bridge.mp (@isolated_contractible.{u}), rejected, isolated_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, isolated_rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def isolatedRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isolated_contractible.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteForestIndependence.isolatedUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteForestIndependence.isolatedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨isolatedArena⟩
  objectArena := .source ⟨isolatedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source isolatedArena ⟨isolatedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G => nativeSet p G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms classificationFamily
#print axioms isolatedFamily
end Reg.D5.S3.Geometry.FiniteForestIndependence
