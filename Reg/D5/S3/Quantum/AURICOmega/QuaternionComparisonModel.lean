import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.Support.DependentFamily

/-! Source-bound audit of the component formula for the quaternion inner product, and
full-telescope source applications for the four closed statements about the model.
Those applications supply only the original statements; they supply no enrolled-template
readout, source selection, whole-family intervention, sensitivity or observational dependence.
The unfinished registrations are tracked at
https://github.com/the-omega-institute/trureturing/issues/31741. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

namespace InnerComponents

/-- Observe the real inner product against a fixed first quaternion. -/
abbrev signature : Signature where
  Params := ℍ[ℝ]
  State _ := ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => ⟪p, s⟫_ℝ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete telescope of `inner_eq_components`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p q : ℍ[ℝ],
    r.readout () p q = p.re * q.re + p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 0, ?_⟩
  change ⟪(1 : ℍ[ℝ]), 1⟫_ℝ ≠ ⟪(1 : ℍ[ℝ]), 0⟫_ℝ
  rw [inner_eq_components, inner_eq_components]
  norm_num

def source_registration : Registration arena (type_of% inner_eq_components) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inner_eq_components, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end InnerComponents

def inner_eq_components_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      inner_eq_components (Realization InnerComponents.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_eq_components_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.InnerComponents.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨InnerComponents.arena⟩
  objectArena := .source ⟨InnerComponents.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source InnerComponents.arena ⟨InnerComponents.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize InnerComponents.signature
    (fun _ p s => ⟪p, s⟫_ℝ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


abbrev noncommutativeSourceScope : Prop := type_of% quaternionModel_noncommutative

theorem noncommutative_source_application : noncommutativeSourceScope :=
  quaternionModel_noncommutative

abbrev touchesZeroSourceScope : Prop := type_of% quaternionModel_touchesZero

theorem touchesZero_source_application : touchesZeroSourceScope :=
  quaternionModel_touchesZero

abbrev chainConnectedSourceScope : Prop := type_of% quaternionModel_chainConnected

theorem chainConnected_source_application : chainConnectedSourceScope :=
  quaternionModel_chainConnected

abbrev hasFeatureRankFiveSourceScope : Prop := type_of% quaternionModel_hasFeatureRank_five

theorem hasFeatureRank_five_source_application : hasFeatureRankFiveSourceScope :=
  quaternionModel_hasFeatureRank_five

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
