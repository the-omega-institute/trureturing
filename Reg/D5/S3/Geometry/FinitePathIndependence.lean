import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FinitePathIndependence

/-! The three vertex-count readouts in the complete native path classification.
Each role retains its original universally quantified index. Interventions change
one whole count family, while the empty clause and all native spaces stay in Law. -/

noncomputable section
open ContinuousMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry

namespace Reg.D5.S3.Geometry.FinitePathIndependence

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool ⊕ Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ k =>
    Sum.elim (fun b => Bool.rec (3 * (k + 1)) (3 * k + 1) b)
      (fun _ => 3 * k + 2) i)
    (fun e => nomatch e)

def intervene (i : Bool ⊕ Unit) : Realization signature :=
  realize signature (fun j p k => if j = i then 0 else actual.readout j p k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    IsEmpty (FiniteCoordinateTruncation.Ispace (SimpleGraph.pathGraph 0)) ∧
    (∀ k : ℕ, Nonempty (FiniteCoordinateTruncation.Ispace
      (SimpleGraph.pathGraph (R.readout (.inl false) () k)) ≃ₕ EuclideanSphereJoin.StdSphere k)) ∧
    (∀ k : ℕ, ContractibleSpace (FiniteCoordinateTruncation.Ispace
      (SimpleGraph.pathGraph (R.readout (.inl true) () k)))) ∧
    (∀ k : ℕ, Nonempty (FiniteCoordinateTruncation.Ispace
      (SimpleGraph.pathGraph (R.readout (.inr ()) () k)) ≃ₕ EuclideanSphereJoin.StdSphere k))

private theorem bridge :
    (type_of% (_root_.D5.S3.Geometry.FinitePathIndependence.classification)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law (i : Bool ⊕ Unit) : ¬ arena.Law (intervene i) := by
  intro h
  have he := _root_.D5.S3.Geometry.FinitePathIndependence.classification.1
  rcases i with (b | ⟨⟩)
  · cases b
    · obtain ⟨e⟩ := h.2.1 0
      exact he.false (e.invFun (EuclideanSphereJoin.coordinatePoint 0))
    · letI : ContractibleSpace (FiniteCoordinateTruncation.Ispace
          (SimpleGraph.pathGraph 0)) := h.2.2.1 0
      obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
        (FiniteCoordinateTruncation.Ispace (SimpleGraph.pathGraph 0))
      exact he.false (e.invFun ())
  · obtain ⟨e⟩ := h.2.2.2 0
    exact he.false (e.invFun (EuclideanSphereJoin.coordinatePoint 0))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  rcases i with (b | u)
  · cases b <;> decide
  · cases u
    decide

def family : Registration arena
    (type_of% (_root_.D5.S3.Geometry.FinitePathIndependence.classification)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp _root_.D5.S3.Geometry.FinitePathIndependence.classification,
    intervene (.inl false), rejected_law (.inl false)⟩
  sensitivity := ⟨fun i => ⟨intervene i,
    fun j h => by funext p k; simp [intervene, realize, h], rfl, rejected_law i⟩,
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
  readout := some (realize signature (fun i _ k =>
    Sum.elim (fun b => Bool.rec (3 * (k + 1)) (3 * k + 1) b)
      (fun _ => 3 * k + 2) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FinitePathIndependence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "fn", "arg", "body", "arg", "fn", "fn", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "arg", "arg", "body", "arg", "fn", "fn", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FinitePathIndependence
