import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCoordinateTruncation

/-! Nonnegative cutoff over the complete finite coordinate family. -/
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateTruncation

namespace Reg.D5.S3.Geometry.FiniteCoordinateTruncation
universe u

structure Parameters where
  V : Type u
  threshold : ℝ

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
  realize signature (fun _ p x => cut p.threshold x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (e : ℝ) (x : V → ℝ) (a : V), 0 ≤ R.readout () ⟨V, e⟩ x a

private theorem bridge : (type_of% (@cut_nonneg.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv e x a
    exact @h V fv dv e x a
  · intro h V fv dv e x a
    exact @h V fv dv e x a

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, 0⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance 0 (fun _ => 0) ⟨()⟩
  change (0 : ℝ) ≤ -1 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨testParameters, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (⟨()⟩ : testParameters.{u}.V)
  change cut 0 (fun _ : testParameters.{u}.V => 0) ⟨()⟩ =
    cut 0 (fun _ : testParameters.{u}.V => 1) ⟨()⟩ at hh
  norm_num [cut] at hh

def family : Registration arena.{u} (type_of% (@cut_nonneg.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@cut_nonneg.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cut_nonneg.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCoordinateTruncation.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCoordinateTruncation.family
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
    (fun _ p x => cut p.threshold x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteCoordinateTruncation
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteCoordinateTruncation
