import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
import Reg.Support.DependentFamily

/-! Source-bound audits of the polar form of unit quaternions and of de Moivre's formula.

The rejected law of the polar form fails at the unit quaternion `1`; the rejected law of de
Moivre's formula fails at the exponent `0` for the unit imaginary quaternion `i`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar

open _root_.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The quaternion unit `i` has real part zero. -/
theorem re_unitI : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]).re = 0 := rfl

/-- The quaternion unit `i` has norm one. -/
theorem norm_unitI : ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ = 1 := by
  have h : ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ * ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    norm_num
  nlinarith [norm_nonneg (⟨0, 1, 0, 0⟩ : ℍ[ℝ])]

/-! The right-hand side `cos θ + sin θ • n` of the polar form, against the axis `n`, for
`exists_eq_cos_arccos_add_sin_smul`. -/
namespace Polar

abbrev signature : Signature where
  Params := ℍ[ℝ]
  State _ := ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ q s => ((Real.cos (Real.arccos q.re) : ℝ) : ℍ[ℝ]) + Real.sin (Real.arccos q.re) • s)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete quaternion, norm hypothesis and axis telescope of
`exists_eq_cos_arccos_add_sin_smul`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ q : ℍ[ℝ], ‖q‖ = 1 →
    ∃ n : ℍ[ℝ], n.re = 0 ∧ ‖n‖ = 1 ∧ q = r.readout () q n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hre, -, hq⟩ := h 1 norm_one
  change (1 : ℍ[ℝ]) = n at hq
  have h1 := congrArg (fun z : ℍ[ℝ] => z.re) hq
  rw [Quaternion.re_one, hre] at h1
  exact one_ne_zero h1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, fun h => ?_⟩
  have h' := congrArg (fun z : ℍ[ℝ] => z.imI) h
  simp [actual, realize, Real.arccos_zero] at h'

def source_registration :
    Registration arena (type_of% @exists_eq_cos_arccos_add_sin_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_eq_cos_arccos_add_sin_smul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Polar

/-! The power `(cos θ + sin θ • n) ^ k`, against the exponent `k`, for
`cos_add_sin_smul_pow`. -/
namespace DeMoivre

abbrev signature : Signature where
  Params := Σ _ : ℍ[ℝ], ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p s => (((Real.cos p.2 : ℝ) : ℍ[ℝ]) + Real.sin p.2 • p.1) ^ s)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete axis, hypothesis, angle and exponent telescope of
`cos_add_sin_smul_pow`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℍ[ℝ], n.re = 0 → ‖n‖ = 1 → ∀ (θ : ℝ) (k : ℕ),
    r.readout () ⟨n, θ⟩ k = ((Real.cos (k * θ) : ℝ) : ℍ[ℝ]) + Real.sin (k * θ) • n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun z : ℍ[ℝ] => z.re) (h _ re_unitI norm_unitI 0 0)
  simp [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨0, 1, 0, 0⟩, Real.pi⟩, 0, 1, fun h => ?_⟩
  have h' := congrArg (fun z : ℍ[ℝ] => z.re) h
  norm_num [actual, realize, Real.cos_pi, Real.sin_pi] at h'

def source_registration :
    Registration arena (type_of% @cos_add_sin_smul_pow) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cos_add_sin_smul_pow, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end DeMoivre

def exists_eq_cos_arccos_add_sin_smul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_eq_cos_arccos_add_sin_smul) (Realization Polar.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar.exists_eq_cos_arccos_add_sin_smul_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar.Polar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Polar.arena⟩
  objectArena := .source ⟨Polar.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Polar.arena ⟨Polar.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Polar.signature
    (fun _ q s => ((Real.cos (Real.arccos q.re) : ℝ) : ℍ[ℝ]) + Real.sin (Real.arccos q.re) • s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def cos_add_sin_smul_pow_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cos_add_sin_smul_pow) (Realization DeMoivre.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar.cos_add_sin_smul_pow_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar.DeMoivre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨DeMoivre.arena⟩
  objectArena := .source ⟨DeMoivre.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source DeMoivre.arena ⟨DeMoivre.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DeMoivre.signature
    (fun _ p s => (((Real.cos p.2 : ℝ) : ℍ[ℝ]) + Real.sin p.2 • p.1) ^ s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
