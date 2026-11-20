import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
import Reg.Support.DependentFamily

/-! Source-bound audits of the left-right translation theorems for unit quaternions and of the
intertwining of unit quaternions with equal real parts. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The unit quaternions `-1` and `1` are different. -/
theorem neg_one_ne_one : (-1 : unitary ℍ[ℝ]) ≠ 1 := fun h => by
  have h' := congrArg (fun z : unitary ℍ[ℝ] => (z : ℍ[ℝ]).re) h
  simp only [Unitary.coe_neg, OneMemClass.coe_one, Quaternion.re_neg, Quaternion.re_one] at h'
  norm_num at h'

/-- The reading separates `1` from its antipode. -/
theorem kappa_one_ne : quaternionModel.kappa 1 1 ≠ quaternionModel.kappa 1 (-1) := by
  intro h
  rw [quaternionModel.kappa_self] at h
  exact neg_one_ne_one ((quaternionModel.kappa_eq_one_iff 1 (-1)).1 h.symm).symm

/-! The reading against a fixed first argument, for `kappa_mul_mul`. -/
namespace Reading

abbrev signature : Signature where
  Params := unitary ℍ[ℝ]
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ x s => quaternionModel.kappa x s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete argument telescope of `kappa_mul_mul`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p q x y : unitary ℍ[ℝ],
    quaternionModel.kappa (p * x * q) (p * y * q) = r.readout () x y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 1 1
  rw [quaternionModel.kappa_self] at hh
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, 1, -1, kappa_one_ne⟩

def source_registration : Registration arena (type_of% @kappa_mul_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kappa_mul_mul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reading

/-! The left-right translation by the two witnesses, for `exists_mul_mul_eq_of_kappa_eq`. -/
namespace Translation

abbrev signature : Signature where
  Params := Σ _ : unitary ℍ[ℝ], unitary ℍ[ℝ]
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := unitary ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => p.1 * s * p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete argument telescope of `exists_mul_mul_eq_of_kappa_eq`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y x' y' : unitary ℍ[ℝ],
    quaternionModel.kappa x y = quaternionModel.kappa x' y' →
      ∃ p q : unitary ℍ[ℝ], r.readout () ⟨p, q⟩ x = x' ∧ p * y * q = y'

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, q, hx, -⟩ := h 1 1 (-1) (-1)
    (by rw [quaternionModel.kappa_self, quaternionModel.kappa_self])
  exact neg_one_ne_one hx.symm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 1, -1, fun h => neg_one_ne_one ?_⟩
  have h' : (1 : unitary ℍ[ℝ]) * 1 * 1 = 1 * -1 * 1 := h
  simpa only [mul_one, one_mul] using h'.symm

def source_registration : Registration arena (type_of% @exists_mul_mul_eq_of_kappa_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_mul_mul_eq_of_kappa_eq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Translation

/-! Left multiplication by the intertwining witness, for `exists_unitary_mul_eq_mul`. -/
namespace Intertwining

abbrev signature : Signature where
  Params := unitary ℍ[ℝ]
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := unitary ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c s => c * s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ c _ => -c) (fun e => nomatch e)

/-- Retain the complete argument telescope of `exists_unitary_mul_eq_mul`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ a a' : unitary ℍ[ℝ], (a : ℍ[ℝ]).re = (a' : ℍ[ℝ]).re →
    ∃ c : unitary ℍ[ℝ], r.readout () c a = a' * c

/-- For `a = a' = 1` the rejected law asks for a unit quaternion `c` with `-c = c`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc⟩ := h 1 1 rfl
  have hc' : -c = c := by
    change -c = 1 * c at hc
    rwa [one_mul] at hc
  have h1 := congrArg (fun z : unitary ℍ[ℝ] => z * c⁻¹) hc'
  simp only [neg_mul, mul_inv_cancel] at h1
  exact neg_one_ne_one h1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, -1, fun h => neg_one_ne_one ?_⟩
  have h' : (1 : unitary ℍ[ℝ]) * 1 = 1 * -1 := h
  simpa only [mul_one, one_mul] using h'.symm

def source_registration : Registration arena (type_of% @exists_unitary_mul_eq_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitary_mul_eq_mul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Intertwining

def kappa_mul_mul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kappa_mul_mul) (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.kappa_mul_mul_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Reading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Reading.arena⟩
  objectArena := .source ⟨Reading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Reading.arena ⟨Reading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature
    (fun _ x s => quaternionModel.kappa x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_mul_mul_eq_of_kappa_eq_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_mul_mul_eq_of_kappa_eq) (Realization Translation.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.exists_mul_mul_eq_of_kappa_eq_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Translation.arena⟩
  objectArena := .source ⟨Translation.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Translation.arena ⟨Translation.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Translation.signature
    (fun _ p s => p.1 * s * p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
    definition := none
    coordinates := #[5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_unitary_mul_eq_mul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_unitary_mul_eq_mul) (Realization Intertwining.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.exists_unitary_mul_eq_mul_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Intertwining.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Intertwining.arena⟩
  objectArena := .source ⟨Intertwining.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Intertwining.arena ⟨Intertwining.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Intertwining.signature
    (fun _ c s => c * s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
