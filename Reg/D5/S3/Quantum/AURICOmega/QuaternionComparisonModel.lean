import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.Support.DependentFamily

/-! Source-bound audits of the component formula for the quaternion inner product, of the inner
product of features and of the radius of the sphere of unit quaternions, and full-telescope source applications for the four
closed statements about the model.
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


/-! The half-shifted inner product against a fixed first quaternion, for `inner_feature`. -/
namespace FeatureReading

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
  realize signature (fun _ p s => (1 + ⟪p, s⟫_ℝ) / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete argument telescope of `inner_feature`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p q : ℍ[ℝ], ⟪feature p, feature q⟫_ℝ = r.readout () p q

/-- The features of zero have inner product one half, not two. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ⟪feature 0, feature 0⟫_ℝ = 2 := h 0 0
  rw [inner_feature, inner_zero_left] at hh
  norm_num at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 0, ?_⟩
  change (1 + ⟪(1 : ℍ[ℝ]), 1⟫_ℝ) / 2 ≠ (1 + ⟪(1 : ℍ[ℝ]), 0⟫_ℝ) / 2
  rw [inner_zero_right, real_inner_self_eq_norm_sq, norm_one]
  norm_num

def source_registration : Registration arena (type_of% inner_feature) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inner_feature, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end FeatureReading

def inner_feature_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      inner_feature (Realization FeatureReading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_feature_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.FeatureReading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨FeatureReading.arena⟩
  objectArena := .source ⟨FeatureReading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source FeatureReading.arena ⟨FeatureReading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FeatureReading.signature
    (fun _ p s => (1 + ⟪p, s⟫_ℝ) / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! The radius of the sphere in `coe_unitary_eq_sphere`. -/
namespace SphereRadius

/-- Observe the sphere about zero in the quaternions as a function of its radius. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => Metric.sphere (0 : ℍ[ℝ]) r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Metric.sphere (0 : ℍ[ℝ]) 2) (fun e => nomatch e)

/-- Retain the complete statement of `coe_unitary_eq_sphere`. -/
abbrev arena : Arena where
  signature := signature
  Law r := (unitary ℍ[ℝ] : Set ℍ[ℝ]) = r.readout () () 1

/-- The quaternion one is a unit quaternion of norm one, not two. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : (unitary ℍ[ℝ] : Set ℍ[ℝ]) = Metric.sphere (0 : ℍ[ℝ]) 2 := h
  have h2 : (1 : ℍ[ℝ]) ∈ (unitary ℍ[ℝ] : Set ℍ[ℝ]) := one_mem (unitary ℍ[ℝ])
  rw [h', mem_sphere_zero_iff_norm, norm_one] at h2
  norm_num at h2

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, fun h => ?_⟩
  have h' : Metric.sphere (0 : ℍ[ℝ]) 1 = Metric.sphere (0 : ℍ[ℝ]) 2 := h
  have h2 : (1 : ℍ[ℝ]) ∈ Metric.sphere (0 : ℍ[ℝ]) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_one]
  rw [h', mem_sphere_zero_iff_norm, norm_one] at h2
  norm_num at h2

def source_registration : Registration arena (type_of% coe_unitary_eq_sphere) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coe_unitary_eq_sphere, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end SphereRadius

def coe_unitary_eq_sphere_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      coe_unitary_eq_sphere (Realization SphereRadius.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.coe_unitary_eq_sphere_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.SphereRadius.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨SphereRadius.arena⟩
  objectArena := .source ⟨SphereRadius.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source SphereRadius.arena ⟨SphereRadius.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize SphereRadius.signature
    (fun _ _ r => Metric.sphere (0 : ℍ[ℝ]) r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
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
