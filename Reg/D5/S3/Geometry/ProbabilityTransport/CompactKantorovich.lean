import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.ProbabilityTransport.CompactKantorovich

/-! Source-bound audit of the real equality in full compact Kantorovich duality. -/

namespace Reg.D5.S3.Geometry.ProbabilityTransport.CompactKantorovich

open MeasureTheory
open _root_.CompactKantorovich
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ left right => left = right) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ left right => left ≠ right) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (_hc : Continuous c),
    r.readout () () (sInf (primalValues μ ν c))
      (sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)})

theorem source_bridge :
    (type_of% @kantorovich_duality_compact.{u,v}) ↔ arena.{u,v}.Law actual := Iff.rfl

theorem actual_law : arena.{u,v}.Law actual :=
  source_bridge.mp (@kantorovich_duality_compact.{u,v})

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let μ : ProbabilityMeasure (ULift.{u} Unit) := ⟨Measure.dirac (ULift.up ()), Measure.dirac.isProbabilityMeasure⟩
  let ν : ProbabilityMeasure (ULift.{v} Unit) := ⟨Measure.dirac (ULift.up ()), Measure.dirac.isProbabilityMeasure⟩
  exact h μ ν (fun _ => 0) continuous_const
    (kantorovich_duality_compact μ ν (fun _ => 0) continuous_const)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

def source_registration :
    Registration arena.{u,v} (type_of% @kantorovich_duality_compact.{u,v}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kantorovich_duality_compact.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.ProbabilityTransport.CompactKantorovich.unit
  realizationName :=
    `Reg.D5.S3.Geometry.ProbabilityTransport.CompactKantorovich.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.ProbabilityTransport.CompactKantorovich
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Geometry.ProbabilityTransport.CompactKantorovich
