import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FinitePathIndependence

/-! The complete path law on native realization sets, with whole-family variation.
The source selector attempts the literal native-space observation in the empty
clause; this is a type-valued observation, rather than an underlying set readout. -/

noncomputable section
open Set ContinuousMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry

namespace Reg.D5.S3.Geometry.FinitePathIndependence

abbrev signature : Signature where
  Params := ℕ
  State n := SimpleGraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Fin n → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeSet (n : ℕ) (G : SimpleGraph (Fin n)) : Set (Fin n → ℝ) :=
  FiniteConeCollapse.realization
    (FiniteGraphVertexSubstitution.independenceComplex G).toPreAbstractSimplicialComplex

def actual : Realization signature :=
  realize signature (fun _ n G => nativeSet n G) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    IsEmpty (↥(R.readout () 0 (SimpleGraph.pathGraph 0))) ∧
    (∀ k : ℕ, Nonempty (↥(R.readout () (3 * (k + 1))
      (SimpleGraph.pathGraph (3 * (k + 1)))) ≃ₕ EuclideanSphereJoin.StdSphere k)) ∧
    (∀ k : ℕ, ContractibleSpace (↥(R.readout () (3 * k + 1)
      (SimpleGraph.pathGraph (3 * k + 1))))) ∧
    (∀ k : ℕ, Nonempty (↥(R.readout () (3 * k + 2)
      (SimpleGraph.pathGraph (3 * k + 2))) ≃ₕ EuclideanSphereJoin.StdSphere k))

private theorem bridge :
    (type_of% (_root_.D5.S3.Geometry.FinitePathIndependence.classification)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  haveI : ContractibleSpace (↥(∅ : Set (Fin 1 → ℝ))) := h.2.2.1 0
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (↥(∅ : Set (Fin 1 → ℝ)))
  exact (e.invFun ()).property

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ⊥, ⊤, ?_⟩
  intro h
  let x : Fin 2 → ℝ := fun _ => 1 / 2
  have hm : x ∈ nativeSet 2 (⊥ : SimpleGraph (Fin 2)) := by
    apply (FiniteCoordinateTruncation.realization_iff _ _).mpr
    constructor
    · constructor
      · intro a; norm_num [x]
      · norm_num [x]
    · simp [FiniteCoordinateTruncation.Avoid]
  change nativeSet 2 (⊥ : SimpleGraph (Fin 2)) =
    nativeSet 2 (⊤ : SimpleGraph (Fin 2)) at h
  rw [h] at hm
  have hz := ((FiniteCoordinateTruncation.realization_iff _ _).mp hm).2
    (0 : Fin 2) (1 : Fin 2) (by simp)
  norm_num [x] at hz

def family : Registration arena
    (type_of% (_root_.D5.S3.Geometry.FinitePathIndependence.classification)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp _root_.D5.S3.Geometry.FinitePathIndependence.classification,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    _root_.D5.S3.Geometry.FinitePathIndependence.classification
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FinitePathIndependence.unit
  realizationName := `Reg.D5.S3.Geometry.FinitePathIndependence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n G => nativeSet n G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FinitePathIndependence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FinitePathIndependence
