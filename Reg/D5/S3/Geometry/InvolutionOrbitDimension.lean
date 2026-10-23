import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.InvolutionOrbitDimension

/-! Original-source audit of dimension preservation for every subset and involution. -/
noncomputable section
open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.InvolutionOrbitDimension
namespace Reg.D5.S3.Geometry.InvolutionOrbitDimension
universe u

structure Parameters where
  X : Type u
  metric : MetricSpace X
  second : @SecondCountableTopology X metric.toUniformSpace.toTopologicalSpace
  c : letI := metric; X ≃ᵢ X
  hc : Function.Involutive c
attribute [instance] Parameters.metric Parameters.second

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Set p.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (Orbit p.c p.hc)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => project p.c p.hc '' s) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ s : Set p.X,
    dimH (R.readout () p s) = dimH s

private theorem bridge : (type_of% (@dimH_project.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p s
    exact h p.c p.hc s
  · intro h X metric second c hc s
    exact h ⟨X, metric, second, c, hc⟩ s

private def realParameters : Parameters.{u} :=
  ⟨ULift.{u} ℝ, inferInstance, inferInstance, IsometryEquiv.refl _, fun _ => rfl⟩
private theorem realDimension : dimH (univ : Set realParameters.{u}.X) = 1 := by
  have hi : Isometry (ULift.down : ULift.{u} ℝ → ℝ) := Isometry.of_dist_eq (fun _ _ => rfl)
  have hh := hi.dimH_image univ
  have hu : ULift.down '' (univ : Set (ULift.{u} ℝ)) = univ := by ext x; simp
  rw [hu, Real.dimH_univ] at hh
  exact hh.symm
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h realParameters univ
  change dimH (∅ : Set (Orbit realParameters.c realParameters.hc)) = _ at hh
  rw [dimH_empty, realDimension] at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨realParameters, ∅, univ, ?_⟩
  intro h
  have hh := congrArg dimH h
  have hs := dimH_project realParameters.c realParameters.hc
  change dimH (project _ _ '' ∅) = dimH (project _ _ '' univ) at hh
  rw [hs, hs, dimH_empty, realDimension] at hh
  norm_num at hh

def family : Registration arena.{u} (type_of% (@dimH_project.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@dimH_project.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dimH_project.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.InvolutionOrbitDimension.__information_unit
  realizationName := `Reg.D5.S3.Geometry.InvolutionOrbitDimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => project p.c p.hc '' s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.InvolutionOrbitDimension
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.InvolutionOrbitDimension
